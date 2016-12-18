load("psort.py")
magma.load("~/sorting.m")   # assumes sorting.m in home directory, change as needed but a path is required

def compare_labels(K,N):
    # set up number field in magma so we can construct ideals
    magma.eval("R<x>:=PolynomialRing(Rationals())")
    magma.eval("K<%s>:=NumberField(%s)"%(K.gen(),K.gen().minpoly()(x)))
    magma.eval("OK:=RingOfIntegers(K)")
    print "Checking ideals of norm up to %s in %s:"%(N,K)
    for n in range(2,N+1):
        S=ideals_of_norm(K,ZZ(n))
        assert len(S) == magma.NumberOfIdealsOfNorm(K,n)
        for I in S:
            assert ideal_label(I) == magma.eval("IdealLabel(ideal<OK|%s,%s>)"%I.gens_two())
        if len(S):
            print "  checked %s ideals of norm %s"%(len(S),n)

K.<a> = NumberField(x^2+1)
compare_labels(K,500)
K.<a> = NumberField(x^3-x+1)
compare_labels(K,1000)
K.<a> = NumberField(x^4 - x^3 + 6*x^2 - 6*x + 6)
compare_labels(K,2000)
K.<a> = NumberField(x^6 + 2*x^4 - 2*x^3 + 4*x^2 + 4*x + 1)
compare_labels(K,2000)
