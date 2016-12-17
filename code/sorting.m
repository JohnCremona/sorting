/*
    Magma code for comparing/sorting/enumerating ideals in the ring of integers OK of a number field.
    The ordering of ideals is described in detail in sorting.tex
    
    IMPORTANT: the ring of integers OK used througout needs to be the ring of integers of a number field
    that was created using the canonical defining polynomial (as listed in the LMFDB and returned by polredabs).
    
    Useful functions in this file:
    
       SplitPrime(p,OK) --              sorted list of the prime OK-ideals dividing (p)
       NumberOfIdealsOfNormQ(q,OK)      counts OK-ideals of prime power norm q
       NumberOfIdealsOfNormN(n,OK)      counts OK-ideals of integer norm n
       IdealsOfNormQ(q,OK)              sorted list of OK-ideals of prime power norm q
       IdealsOfNormN(q,OK)              sorted list of OK-ideals of integer norm n
       IdealOrdinal(I)                  returns m such that I is the mth ideal of its norm
       IdealFromOrdinal(n,m,OK)         returns the mth OK-ideal of norm n
       CompareIdeals(I,J)               returns -1,0,1 as I<J,I=J,I>J in our ordering
*/

function UniqueMax(V)
    m,i:=Max(V);
    return m gt Max([V[j]:j in [1..#V]|j ne i]) select i else 0;
end function;

function ComparepAdicCoefficients(c1,c2,p,k)
    for i:=1 to k do
        c1,d1 := Quotrem(c1,p);  c2,d2 := Quotrem(c2,p);
        if d1 ne d2 then return d1-d2; end if;
    end for;
    return 0;
end function;

function ComparepAdicPolys(h1,h2,p,k)
    if Degree(h1) ne Degree(h2) then return Degree(h1)-Degree(h2); end if;
    c1 := Coefficients(h1);  c2 := Coefficients(h2);
    for i:=1 to k do
        v := ComparepAdicCoefficients(c1[i],c2[i],p,k);
        if v ne 0 then return v; end if;
    end for;
    return 0;
end function;

function ComparePrimeFactors(s1,s2,p,k)
    p1 := s1[1]; p2:=s2[1];
    if Norm(p1) ne Norm(p2) then return Norm(p1)-Norm(p2); end if;
    if RamificationIndex(p1) ne RamificationIndex(p2) then return RamificationIndex(p1)-RamificationIndex(p2); end if;
    if InertiaDegree(p1) ne InertiaDegree(p2) then return InertiaDegree(p1)-InertiaDegree(p2); end if;
    return ComparepAdicPolys (s1[2],s2[2],p,k);
end function;

// Given a prime p and the ring of integers OK of a number field K, returns a list of the prime ideals in OK lying above p
// The list is orderd by norm, ramification index, pAdic-poly, where the pAdic-poly h corresponding to a prime ideal P is the unique
// irreducible factor of g in Zp[x] for which v_P(h(a)) is infinite.  pAdic polys h1 and h2 of the same degree are ordered
// lexicographically according to the p-adic expansions of their coeffs (written in base p with digits in [0,p-1]).
function SplitPrime(p,OK)
    R:=PolynomialRing(Integers());
    p:=Integers()!p;
    error if not IsPrime(p), Sprintf("Input p = %o to SplitPrime is not prime",p);
    if Degree(OK) eq 1 then return [ideal<OK|p>]; end if;
    g:=DefiningPolynomial(OK);
    P:=[s[1]:s in Factorization(ideal<OK|p>)];          // prime ideals dividing p
    if #P eq 1 then return P; end if;                   // if there is only one prime above p, we are done.
    a:=OK.2;
    g:=R!MinimalPolynomial(a);
    assert g eq DefiningPolynomial(OK);
    k := 1;
    while true do
        // compute distinct factors of f in Zp[x]/(p^kZ_p[x])
        Zp:=pAdicRing(p,k);
        // trap precision issues and magma bugs
        try
            factors:=Factorization(ChangeRing(g,Zp));
        catch e
            factors:=[];
        end try;
        if #factors eq 0 then k:=k+1; continue; end if;
        H:=[R!ChangeRing(h[1],quo<Zp|p^k>) : h in factors|h[2] eq 1];
        if #H eq #P then // if factors are distinct
            // if each factor determines a unique prime pp in P for which v_pp((p^k,g(a))) is maximal, we are done
            if #[h:h in H|UniqueMax([Valuation(ideal<OK|p^k,Evaluate(h,a)>,pp):pp in P]) gt 0] eq #P then break; end if;
        end if;
        error if k gt 1000, Sprintf("SplitPrime appears to be stuck in an infinite loop on input p = %o, a prime of %o", p, OK);   // abort if we appear to be stuck
        k:=k+1;
    end while;
    // Normalize polys to coefficients lie in [0,p^k-1]
    H:=[R![c mod p^k : c in Coefficients(h)]:h in H];
    // Match polys and prime ideals
    assert #H eq #P;
    S:=[];
    for h in H do
        I:=ideal<OK|p^k,Evaluate(h,a)>;
        j := UniqueMax([Valuation(I,P[i]) : i in [1..#P]]);
        assert j ne 0;
        assert Degree(h) eq RamificationIndex(P[j])*InertiaDegree(P[j]);
        S:=Append(S,<P[j],h>);
    end for;
    S := Sort(S,func<s1,s2:prime:=p,prec:=k|ComparePrimeFactors(s1,s2,prime,prec)>);
    return [s[1]:s in S];
end function;

// Counts the number of ideals of prime power norm q in the ring of integers OK
// This is faster than actually enumerating them all
function NumberOfIdealsOfNormQ(q,OK)
    q:=Integers()!q;
    b,p,k := IsPrimePower(q);
    error if not b, Sprintf("Input q = %o to NumberOfIdealsOfNormQ is not a prime power.", q);
    V:=[InertiaDegree(a[1]):a in Factorization(ideal<OK|p>)];
    return NumberOfPoints(Polytope([[i eq j select k/V[i] else 0:i in [1..#V]]:j in [1..#V]]));
end function;

// Counts the number of ideals of integer norm n in the number field Q[x]/(g(x))
// This is substantially faster than actually enumerating them all
function NumberOfIdealsOfNormN(n,OK)
    n:=Integers()!n;
    P:=Factorization(n);
    return &*[NumberOfIdealsOfNormQ(p[1]^p[2],OK):p in P];
end function;

// We compare exponent vectors of prime-power norm ideals first by weight (sum) and then
// in reverse lexicogrpahic order (so (1,0) < (0,1) < (2,0) < (1,1) < (0,2) < ...)
function CompareExponentVectors(v,w)
    error if #v ne #w, Sprintf("Attempt to compare vectors %o and %o of different lengths in CompareExponentVectors", v, w);
    if &+v lt &+w then return -1; end if;
    if &+v gt &+w then return 1; end if;
    for i in [1..#v] do
        if v[i] gt w[i] then return -1; end if;
        if v[i] lt w[i] then return 1; end if;
    end for;
    return 0;
end function;

// Returns a list of ideals of prime power norm q in the number field Q[x]/(g(x)) ordered by exponent vector (weight, reverse lex)
function IdealsOfNormQ(q,OK)
    q:=Integers()!q;
    b,p,k := IsPrimePower(q);
    error if not b, Sprintf("Input q = %o to IdealsOfNormQ is not a prime power.", q);
    P:=SplitPrime(p,OK);
    V:=[InertiaDegree(I):I in P];
    S:=[[Vector(v)[i]:i in [1..#V]]:v in Points(Polytope([[i eq j select k/V[i] else 0:i in [1..#V]]:j in [1..#V]]))];
    S:=Sort(S,CompareExponentVectors);
    return [&*[P[i]^(ZZ!Vector(v)[i]):i in [1..#V]]:v in S];
end function;

// Returns a list of ideals of integer norm n in the number field Q[x]/(g(x)) lexicographically ordered according to their factorizations
// into ideals of prime power norm, where ideals of the same prime power norm are ordered by exponent vector (weight, reverse lex)
function IdealsOfNormN(n,OK)
    n:=Integers()!n;
    if n eq 1 then return ideal<OK|1>; end if;
    pp:=[p[1]^p[2]:p in Factorization(n)];
    Q:=<IdealsOfNormQ(q,OK):q in pp>;
    return [&*[I:I in t]:t in CartesianProduct(Q)];
end function;

// Given an OK-ideal I returns the integer m for which I is the mth OK-ideal of norm N(I)
function IdealOrdinal(I)
    n:=Norm(I);
    if n eq 1 then return 1; end if;
    pp:=[p[1]^p[2]:p in Factorization(n)];
    Q:=<IdealsOfNormQ(q,Order(I)):q in pp>;
    A:=<GCD(ideal<Order(I)|q>,I):q in pp>;
    v:=<Index(Q[i],A[i]):i in [1..#pp]>;
    w:=Append([&*[#Q[i]: i in [j+1..#pp]]:j in [1..#pp-1]],1);
    return 1+&+[(v[i]-1)*w[i]:i in [1..#pp]];
end function;

// Given integers n and m and a ring of integers OK, returns the mth OK-ideal of norm n
// Returns 0 if there are no OK-ideals of norm n
function IdealFromOrdinal(n,m,OK)
    n:=Integers()!n; m:=Integers()!m;
    error if n le 0, Sprintf("Invalid norm %o in IdealFromOrdinal",n);
    I:=ideal<OK|1>;
    if n eq 1 then
        error if m ne 1, Sprintf("Invalid ordinal %o for norm %o in IdealFromOrdinal", m,n);
        return I;
    end if;
    pp:=[p[1]^p[2]:p in Factorization(n)];
    Q:=<IdealsOfNormQ(q,OK):q in pp>;
    for S in Q do if #S eq 0 then return 0; end if; end for;
    a := m-1;
    for j:=#Q to 1 by -1 do
        i:=a mod #Q[j];
        I *:= Q[j][i+1];
        a:=ExactQuotient(a-i,#Q[j]);
    end for;
    error if a ne 0, Sprintf("Invalid ordinal %o for norm %o in IdealFromOrdinal", m,n);
    return I;
end function;

function CompareIdeals(I1,I2)
    n1:=Norm(I1); n2:=Norm(I2);
    if n1 lt n2 then return -1; end if;
    if n1 gt n2 then return 1; end if;
    pp:=[p[1]^p[2]:p in Factorization(n1)];
    for q in pp do
        J1:=GCD(I1,ideal<Order(I1)|q>); J2:=GCD(I2,ideal<Order(I2)|q>);
        if J1 ne J2 then
            Q:=IdealsOfNormQ(q,Order(I1));
            if Index(Q,J1) lt Index(Q,J2) then return -1; else return 1; end if;
        end if;
    end for;
    return 0;
end function;

// test function that exercises some of the code above
procedure Test(OK,N)
    cnt:=0;
    for n:=2 to N do
        S:=IdealsOfNormN(n,OK);
        for I in S do
            m:=IdealOrdinal(I);
            printf "%o.%o\n",n,m;
            assert I eq IdealFromOrdinal(n,m,OK);
            if I ne S[#S] then
                assert CompareIdeals(I,IdealFromOrdinal(n,m+1,OK)) eq -1;
            end if;
            cnt+:=1;
        end for;
    end for;
    printf "Successfully checked %o non-trivial ideals of norm up to %o in %o\n", cnt, N, OK;
end procedure;