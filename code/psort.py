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
