def primes_of_degree_iter(K, deg, condition=None, sort_key=None, maxnorm=Infinity):
    for p in primes(2,stop=maxnorm):
        if condition==None or condition(p):
            PP = K.primes_above(p, degree=deg)
            PP.sort(key=sort_key)
            for P in PP:
                if P.norm()<=maxnorm:
                    yield P

def primes_iter(K, condition=None, sort_key=None, maxnorm=Infinity):
    d = K.degree()
    dlist = d.divisors() if K.is_galois() else srange(1,d+1)
    PPs = [primes_of_degree_iter(K,d, condition, sort_key)  for d in dlist]
    Ps = [PP.next() for PP in PPs]
    ns = [P.norm() for P in Ps]
    while True:
        nmin = min(ns)
        if nmin > maxnorm:
            raise StopIteration
        i = ns.index(nmin)
        P = Ps[i]
        Ps[i] = PPs[i].next()
        ns[i] = Ps[i].norm()
        yield P

# sort key for number field elements.  the list() method returns a
# list of the coefficients in terms of the power basis, constant
# first.

nf_key = lambda a: a.list()

# Elements of GF(p) already have a good cmp function

# Sort key for GF(p)[X]

FpX_key = lambda a: a.list()

# Sort key for Z_p.  The start_val=0 is needed for elements whose
# parent is Qp rather than Zp since over Qp the first entry is the
# coefficient of p^v with v the the valuation

Zp_key = lambda a: a.list(start_val=0)

# Sort key for Zp[X].  For example the key for
# (7 + 8*37 + 9*37^2 + O(37^3))*x^2 + (4 + 5*37 + 6*37^2 + O(37^3))*x
# + (1 + 2*37 + 3*37^2 + O(37^3))
# is
# [2, 1, 4, 7, 2, 5, 8, 3, 6, 9]
#
# The degree comes first, followed by the 0'th p-adic digit of each
# coefficient, then the 1st, etc.  The point of the flatten(zip()) is
# essentially to transpose a matrix (list of lists)

# We'll need a key functino which depends on a p-adic precision k, and
# which only uses the p-adic digits up to the coefficient of p^{k-1}:

def ZpX_key(k):
    return lambda f: [f.degree()] + flatten(zip(*[c.list(start_val=0)[:k] for c in f.list()]))

# Sorting primes over a number field K.  The function make_keys(K,p)
# finds and sorts all primes above p, creates a dictionary with keys
# the primes P and values their sort keys [norm,e,i] with i the index
# from 1 in a list of all those primes with the same norm and
# ramification index e.  This is stored in K in a dict called
# psort_dict, whose keys are rational primes p.  Then the main key
# function prime_key(P) will check to see if K already has sorted the
# primes above the prime below p.

def make_keys(K,p):
    if not hasattr(K,'psort_dict'):
        K.psort_dict = {}
    if not p in K.psort_dict:
        # create the sorting dict for primes above p
        key_dict = {}
        Fp = GF(p)
        g = K.defining_polynomial()
        QQx = g.parent()
        a = K.gen()
        PP = K.primes_above(p)

        if not p.divides(g.discriminant()):
            # the easier unramified case
            gfact = [h for h,e in g.change_ring(Fp).factor()]
            gfact.sort(key=FpX_key)
            hh = [QQx(h) for h in gfact]
            for P in PP:
                # exactly one mod-p factor h will be such that P|h(a).
                i = 1 + next((i for i,h in enumerate(hh) if h(a).valuation(P)>0), -1)
                assert i>0
                key_dict[P] = (P.norm(),P.ramification_index(),i)
        else:
            # the general ramified case factor g over Z_p to precision
            # p^k0 until the mod p^k1 reductions of the factors are
            # distinct, with k0 >= k1 >= 1
            k0 = 20
            ok = False
            while not ok:
                gfact = [h for h,e in g.factor_padic(p,k0)]
                nfact = len(gfact)
                gf = [h.lift() for h in gfact]
                k1 = 1
                while (k1<k0) and not ok:
                    hh = [h % p**k1 for h  in gf]
                    ok = len(Set(hh))==nfact
                    if not ok:
                        k1 += 1
                if not ok:
                    k0+=10
            # now hh holds the factors reduced mod p^k1 and these are
            # distinct so we sort the p-adic factors accordingly (these
            # will be first sorted by degree)
            gfact.sort(key=ZpX_key(k1))
            hh = [h.lift() % p**k1 for h  in gfact]
            degs = list(Set([h.degree() for h in gfact]))
            hd = dict([(d,[h for h in hh if h.degree()==d]) for d in degs])

            # Finally we find the index of each prime above p
            for P in PP:
                e = P.ramification_index()
                f = P.residue_class_degree()
                hs = hd[e*f]
                # work out which h in hs matches P
                m = max([h(a).valuation(P) for h in hs])
                i = 1 + next((i for i,h in enumerate(hs) if h(a).valuation(P)==m), -1)
                assert i>0
                key_dict[P] = (P.norm(),e,i)

        K.psort_dict[p] = key_dict

# If P is a prime ideal in a number field this function returns its
# sort key in the form (norm, e, i) with e the ramification index and
# i the index (starting at 1) in the sorted list of all primes with
# the same norm and e.  The first time the function is called for a
# prime of K above any fixed rational prime p, all the sort keys for
# all P above p are computed and stored as an attribute of the field,
# so that the rest can be retrieved instantly.

def prime_key(P):
    p = P.smallest_integer()
    K = P.number_field()
    try:
        return K.psort_dict[p][P]
    except (AttributeError, KeyError):
        make_keys(K,p)
        return K.psort_dict[p][P]

# Using the sort key as above, a label for every prime may be
# constructed.  This version is inadequate since if there are 2 primes
# with the same norm n and different ram. indices then there will be
# more than one with the label n.1.  This would be the case in degree
# 3 if (p) = P*Q^2 where P and Q both have degree 1.

def prime_label(P):
    n, e, i = prime_key(P)
    return "%s.%s" % (n,i)
