#!/usr/bin/env python

# All of the imports
import os
import sys
import time
import random
import socket
import dns.resolver
import dns.message
import dns.query
import dns.rdatatype
import dns.rcode
import dns.dnssec

# Some hardcoded variables
ROOT1 = 'a.root-servers.net'
ROOT2 = 'b.root-servers.net'
ROOT3 = 'c.root-servers.net'
ROOT4 = 'd.root-servers.net'


def get_the_ip(domain):
    return socket.gethostbyname(domain)

ROOTHINTS = {ROOT1: get_the_ip(ROOT1), ROOT2: get_the_ip(ROOT2), ROOT3: get_the_ip(ROOT3), ROOT4: get_the_ip(ROOT4)}
# root server names and addresses

class Cache:
    ZoneDict   = dict()
    NSDict     = dict()


def printCache():

    print("NAMESERVER CACHE")
    for nsname, nsobj in Cache.NSDict.items():
        ipstring_list = " ".join([x.addr for x in nsobj.iplist])
        print("%s %s" % (nsname, ipstring_list))
    return


class Query:
    def __init__(self, qname, qtype, qclass, minimize=False):
        if isinstance(qname, dns.name.Name):
            self.qname = qname
        else:
            self.qname = dns.name.from_text(qname)
        self.orig_qname = self.qname
        self.qtype = qtype
        self.qclass = qclass
        self.minimize = minimize
        self.quiet = False
        self.rcode = None
        self.got_answer = False
        self.cname_chain = []
        self.answer_rrset = []
        self.full_answer_rrset = []

    def print_full_answer(self):
        if self.full_answer_rrset:
            print("\n".join([x.to_text() for x in self.full_answer_rrset]))

    def get_answer_ip_list(self):
        iplist = []
        for rrset in self.answer_rrset:
            if rrset.rdtype in [dns.rdatatype.A, dns.rdatatype.AAAA]:
                for rr in rrset:
                    iplist.append(rr.to_text())
        return iplist

    def set_minimized(self, zone):
        labels_qname = self.orig_qname.labels
        labels_zone = zone.name.labels
        minLabels = len(labels_zone) + 1
        self.qname = dns.name.Name(labels_qname[-minLabels:])

    def prepend_label(self):
        numLabels = len(self.qname) + 1
        self.qname = dns.name.Name(self.orig_qname[-numLabels:])

    def __repr__(self):
        return "<Query: %s,%s,%s>" % (self.qname, self.qtype, self.qclass)


class IPaddress:

    def __init__(self, ip):
        self.addr = ip
        self.addrtype = None
        self.rtt = float('inf')
        self.query_count = 0

    def __repr__(self):
        return "<IPaddress: %s>" % self.addr


class NameServer:

    def __init__(self, name):
        self.name = name
        self.iplist = []

    def has_ip(self, ipstring):
        if ipstring in [x.addr for x in self.iplist]:
            return True
        else:
            return False

    def install_ip(self, ipstring):
        if not self.has_ip(ipstring):
            self.iplist.append(IPaddress(ipstring))
        return

    def __repr__(self):
        return "<NS: %s>" % self.name


class Zone:
    def __init__(self, zone):
        self.name = zone
        self.nslist = []
        Cache.ZoneDict[zone] = self

    def has_ns(self, ns):
        if ns in self.nslist:
            return True
        else:
            return False

    def install_ns(self, nsname, clobber=False):
        if nsname not in self.nslist:
            self.nslist.append(nsname)
        if clobber or (nsname not in Cache.NSDict):
            Cache.NSDict[nsname] = NameServer(nsname)
        return Cache.NSDict[nsname]

    def iplist(self):
        result = []
        for ns in self.nslist:
            result += Cache.NSDict[ns].iplist
        return result

    def iplist_sorted_by_rtt(self):
        return sorted(self.iplist(), key = lambda ip: ip.rtt)

    def print_details(self):
        print("*** STARTING NEXT ITERATION WITH DOMAIN: %s" % self.name)
        for nsname in self.nslist:
            nsobj = Cache.NSDict[nsname]
            addresses = [x.addr for x in nsobj.iplist]
            print("%s %s %s" % (self.name, nsobj.name, addresses))
        return

    def __repr__(self):
        return "<Zone: %s>" % self.name


def get_root_zone():
    z = Zone(dns.name.root)
    for key, value in ROOTHINTS.iteritems():
        name = dns.name.from_text(key)
        nsobj = z.install_ns(name, clobber=False)
        nsobj.install_ip(value)
    return z


def closest_zone(qname):

    for z in reversed(sorted(Cache.ZoneDict.keys())):
        if qname.is_subdomain(z):
            return Cache.ZoneDict[z]
    else:
        return Cache.ZoneDict[dns.name.root]


def get_ns_addrs(zone, message):

    needsGlue = []
    for nsname in zone.nslist:
        if nsname.is_subdomain(zone.name):
            needsGlue.append(nsname)
    needToResolve = list(set(zone.nslist) - set(needsGlue))

    for rrset in message.additional:
        if rrset.rdtype in [dns.rdatatype.A, dns.rdatatype.AAAA]:
            name = rrset.name
            for rr in rrset:
                if not zone.has_ns(name):
                    continue
                if (not True) or (name in needsGlue):
                    nsobj = Cache.NSDict[name]
                    nsobj.install_ip(rr.address)

    if not zone.iplist() or True:
        for name in needToResolve:
            nsobj = Cache.NSDict[name]
            if nsobj.iplist:
                continue
            for addrtype in ['A', 'AAAA']:
                nsquery = Query(name, addrtype, 'IN', False)
                nsquery.quiet = True
                resolve_name(nsquery, closest_zone(nsquery.qname), inPath=False, nsQuery=True)
                for ip in nsquery.get_answer_ip_list():
                    nsobj.install_ip(ip)

    return


def process_referral(message, query):

    for rrset in message.authority:
        if rrset.rdtype == dns.rdatatype.NS:
            break
    else:
        print("ERROR: unable to find NS RRset in referral response")
        return None

    zonename = rrset.name
    if zonename in Cache.ZoneDict:
        zone = Cache.ZoneDict[zonename]
    else:
        zone = Zone(zonename)
        for rr in rrset:
            nsobj = zone.install_ns(rr.target)

    get_ns_addrs(zone, message)
    return zone


def process_answer(response, query, addResults=None):

    answer = response.answer
    if query.qname != query.orig_qname:
        return answer

    empty_answer = (len(answer) == 0)
    if empty_answer:
        if not query.quiet:
            print("ERROR: NODATA: %s of type %s not found" % \
                  (query.qname, query.qtype))

    for rrset in answer:
        if rrset.rdtype == dns.rdatatype.from_text(query.qtype) and \
           rrset.name == query.qname:
            query.answer_rrset.append(rrset)
            addResults and addResults.full_answer_rrset.append(rrset)
            query.got_answer = True
        elif rrset.rdtype == dns.rdatatype.DNAME:
            query.answer_rrset.append(rrset)
            addResults and addResults.full_answer_rrset.append(rrset)
            print(rrset.to_text())
        elif rrset.rdtype == dns.rdatatype.CNAME:
            query.answer_rrset.append(rrset)
            addResults and addResults.full_answer_rrset.append(rrset)
            print(rrset.to_text())
            cname = rrset[0].target
            print("CNAME found, resolving canonical name %s" % cname)
            cname_query = Query(cname, query.qtype, query.qclass, False)
            addResults and addResults.cname_chain.append(cname_query)
            resolve_name(cname_query, closest_zone(cname), inPath=False, addResults=addResults)

    return answer


def process_response(response, query, addResults=None):

    rc = None; ans = None; referral = None
    if not response:
        return (rc, ans, z)
    rc = response.rcode()
    query.rcode = rc
    aa = (response.flags & dns.flags.AA == dns.flags.AA)
    if rc == dns.rcode.NOERROR:
        answerlen = len(response.answer)
        if answerlen == 0 and not aa:                    # Referral
            referral = process_referral(response, query)
        else:                                            # Answer
                ans = process_answer(response, query, addResults=addResults)
    elif rc == dns.rcode.NXDOMAIN:                       # NXDOMAIN
        if not query.quiet:
            print("ERROR: NXDOMAIN: %s not found" % query.qname)
    return (rc, ans, referral)


def update_query_counts(ip, nsQuery=False, tcp=False):
    ip.query_count += 1
    return


def send_query(query, zone, nsQuery=False):

    response = None
    print("***COMMAND: %s %s %s at zone %s" % \
               (query.qname, query.qtype, query.qclass, zone.name))
    msg = dns.message.make_query(query.qname, query.qtype, rdclass=query.qclass)
    msg.flags ^= dns.flags.RD
    nsaddr_list = zone.iplist_sorted_by_rtt();

    if len(nsaddr_list) == 0:
        print("ERROR: No nameserver addresses found for zone: %s." % zone.name)
        return response

    for nsaddr in nsaddr_list:

        print("*** QUERYING ZONE %s AT ADDRESS %s" % (zone.name, nsaddr.addr))
        try:
            update_query_counts(ip=nsaddr, nsQuery=nsQuery)
            msg.id = random.randint(1,65535)          # randomize txid
            truncated = False
            t1 = time.time()
            response = dns.query.udp(msg, nsaddr.addr)
            t2 = time.time()
            nsaddr.rtt = (t2 - t1)
            truncated = (response.flags & dns.flags.TC == dns.flags.TC)
            print response
            print("*** LATENCY %s" % (nsaddr.rtt))

        except Exception as e:
            print("Query failed: %s (%s, %s)" % (nsaddr.addr, type(e).__name__, e))
            pass
        else:
            rc = response.rcode()
            if rc not in [dns.rcode.NOERROR, dns.rcode.NXDOMAIN]:
                print("WARNING: response %s from %s" % (dns.rcode.to_text(rc), nsaddr.addr))
            else:
                break
    else:
        print("ERROR: Queries to all servers for zone %s failed." % zone.name)

    return response

def resolve_name(query, zone, inPath=True, nsQuery=False, addResults=None):

    curr_zone = zone
    repeatZone = False
    curr_zone.print_details()

    if query.minimize:
        if repeatZone:
            query.prepend_label()
            repeatZone = False
        else:
            query.set_minimized(curr_zone)
    response = send_query(query, curr_zone, nsQuery=nsQuery)
    if not response:
        return
    rc, ans, referral = process_response(response, query, addResults=addResults)
    if rc == dns.rcode.NXDOMAIN:
        repeatZone = True
    if not referral:
        repeatZone = True
    else:
        curr_zone = referral
    return

def badass(RootZone):

    with open(sys.argv[1]) as f:
        for line in f:
            parts = line.split()
            if parts[0].find("print") != -1:
                printCache()
            if parts[0].find("resolve") != -1:
                qname = parts[1]
                qtype = parts[2]
                qclass = 'IN'
            elif parts[0].find("quit") != -1:
                sys.exit(0)
            else:
                pass
                continue
            query = Query(qname, qtype, qclass, minimize=False)
            starting_zone = closest_zone(query.qname)
            resolve_name(query, starting_zone, addResults=query)
            query.print_full_answer()
    return

if __name__ == '__main__':

    random.seed(os.urandom(64))
    RootZone = get_root_zone()
    badass(RootZone)
    sys.exit(0)