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

# We need a key function which depends on a p-adic precision k, and
# which only uses the p-adic digits up to the coefficient of p^{k-1}.
# We use our own version of Sage's c.padded_list(k) which does not
# always start with the p^0 coefficient.

def padded_list(c,k):
    a = c.list(start_val=0)
    return a[:k] + [ZZ(0)]* (k-len(a))

def ZpX_key(k):
    return lambda f: [f.degree()] + flatten(zip(*[padded_list(c,k) for c in f.list()]))

# Sorting primes over a number field K.

def make_keys(K,p):
    """Find and sort all primes of K above p, and store their sort keys in
    a dictionary with keys the primes P and values their sort keys
    (n,j,e,i) with n the norm, e the ramificatino index, i the index
    (from 1) in the list of all those primes with the same (n,e), and
    j the index (from 1) in the sorted list of all with the same norm.
    This dict is stored in K in a dict called psort_dict, whose keys
    are rational primes p.
    """
    if not hasattr(K,'psort_dict'):
        K.psort_dict = {}
    if not p in K.psort_dict:
        print("creating keys for primes above {}".format(p))
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
            print("p-adic factors: {}".format(gfact))
            print("with keys {}".format([ZpX_key(k1)(h) for h in gfact]))
            hh = [h.lift() % p**k1 for h  in gfact]
            print("p-adic factors mod {}^{}: {}".format(p,k1,hh))
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

        # Lastly we add a field j to each key (n,e,i) -> (n,j,e,i)
        # which is its index in the sublist withe same n-value.  This
        # will not affect sorting but is used in the label n.j.

        vals = key_dict.values()
        ns = Set([n for n,e,i in vals])
        new_key_dict = {}
        for P in key_dict:
            k = key_dict[P]
            j = 1 + sorted([v for v in vals if v[0]==k[0]]).index(k)
            new_key_dict[P] = (k[0],j,k[1],k[2])

        K.psort_dict[p] = new_key_dict

def prime_key(P):
    """Return the key (n,j,e,i) of a prime ideal P, where n is the norm, e
    the ramification index, i the index in the sorted list of primes
    with the same (n,e) and j the index in the sorted list or primes
    with the same n.

    The first time this is called for a prime P above a rational prime
    p, all the keys for all primes above p are computed and stored in
    the number field, by the make_keys function.
    """
    p = P.smallest_integer()
    K = P.number_field()
    try:
        return K.psort_dict[p][P]
    except (AttributeError, KeyError):
        make_keys(K,p)
        return K.psort_dict[p][P]

def prime_label(P):
    """ Return the label of a prime ideal.
    """
    n, j, e, i = prime_key(P)
    return "%s.%s" % (n,j)


def prime_from_label(K, lab):
    """Return the prime of K from a label, or 0 is there is no such prime
    """
    n, j = [ZZ(c) for c in lab.split(".")]
    p, f = n.factor()[0]
    make_keys(K,p)
    d = K.psort_dict[p]
    try:
        return next((P for P in d if d[P][:2]==(n,j)))
    except StopIteration:
        return 0

def primes_of_degree_iter(K, deg, condition=None, sort_key=prime_label, maxnorm=Infinity):
    """Iterator through primes of K of degree deg, sorted using the
    provided sort key, optionally with an upper bound on the norm.  If
    condition is not None it should be a True/False function on
    rational primes, inwhich case only primes P dividing p for which
    condition(p) holds will be returned.  For example,
    condition=lambda:not p.divides(6).
    """
    for p in primes(2,stop=maxnorm):
        if condition==None or condition(p):
            for P in sorted(K.primes_above(p, degree=deg), key=sort_key):
                if P.norm()<=maxnorm:
                    yield P

def primes_iter(K, condition=None, sort_key=prime_label, maxnorm=Infinity):
    """Iterator through primes of K, sorted using the provided sort key,
    optionally with an upper bound on the norm.  If condition is not
    None it should be a True/False function on rational primes,
    inwhich case only primes P dividing p for which condition(p) holds
    will be returned.  For example, condition=lambda:not p.divides(6).
    """
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

