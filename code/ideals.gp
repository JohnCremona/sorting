/* ideals.gp */

/*

main functions

ideal2label(nf,x)
label2ideal(nf,lab)

nbidealsofnorm(nf,N)
idealsofnorm(nf,N,Lp=[],Ldec=[])
idealsupto(nf,x)

*/

/** list and sorting utilities **/

\\for compatibility with older versions of gp
sublist(v,a,b) =
{
  a = max(a,1);
  b = min(b,#v);
  if(#v==0 || b<a, return([]));
  v[a..b];
}

\\sort polynomials in Zp[X] of the same degree
\\return 0 if not enough precision
\\o/w return permutation
\\polynomials assumed to be monic and distinct
\\known up to O(p^r)
sortpadic(L,p,r,L2=[[]|i<-[1..#L]]) =
{
 my(perm,k);
 perm = [];
 \\print(L);
 L = [liftint(Vec(polrecip(P))) | P <- L];
 L = [v[1..#v-1] | v <- L];
 k = -1;
 while(k<r && #perm<#L,
  L2 = [concat(L2[i],L[i]%p) | i <- [1..#L]];
  L \= p;
  perm = vecsort(L2,,1+8);
  k+=1;
  \\print(k, " ", L2, " ", perm)
 );
 if(k>=r, 0, perm);
}

\\auxiliary functions
weightrev(L) =
{
  [concat([vecsum(v)],-v) | v <- L];
}
\\ componentwise max
maxes(L) =
{
  my(M = L[1]);
  for(i=2,#L,
    for(j=1,#M,
      if(L[i][j]>M[j],M[j]=L[i][j])
    )
  );
  M;
}



/** useful combinatorics **/

\\number of solutions x_i>=0 to sum_i a_i x_i = k (a_i>0, k>=0)
nbintlinsols(a,k) =
{
  my(P,T = 'T);
  P = prod(i=1,#a,1/(1-T^a[i]+O(T^(k+1))));
  polcoeff(P,k);
}

\\list of solutions x_i>=0 to sum_i a_i x_i = k (a_i>0, k>=0)
intlinsols(a,k) =
{
  my(n = #a,L = [], L2);
  if(n==1,
    if(k%a[1], return([]), return([[k\a[1]]]))
  );
  for(xn=0,k\a[n],
    L2 = intlinsols(a[1..n-1],k-xn*a[n]);
    L = concat(L, [concat(v,[xn]) | v <- L2])
  );
  L;
}

\\number of solutions x_i>=0 to:
\\  sum_i a_i x_i = k
\\  sum_i x_i = w
\\  (a_i>0, k>0)
\\flag=1: returns the vector of number of solutions of weights [1..w]
nbintlinsols2(a,k,w,flag=0) =
{
  my(P, S = 'S, T = varhigher("T",S),v);
  P = prod(i=1, #a, sum(j=0,k\a[i],(S^j+O(S^(w+1)))*T^(a[i]*j)) + O(T^(k+1)) );
  if(flag,
    v = Vecrev(Pol(polcoeff(P,k)));
    if(#v<w+1, v = concat(v,[0|i<-[1..w+1-#v]]));
    sublist(v,2,w+1),
  \\else
    polcoeff(polcoeff(P,k),w)
  );
}

\\match prime ideals and polynomials
\\ha = h(a), h p-adic factor of minimal polynomial of a
\\return 0 if not enough precision
nfprimematch(nf,ha,p,r,dec=idealprimedec(nf,p)) =
{
 my(cand);
 \\print("vals: ",[min(nfeltval(nf,ha,pr),(r-1)*pr.e) | pr<-dec]);
 cand = [pr | pr <- dec, nfeltval(nf,ha,pr) >= (r-1)*pr.e];
 if(#cand!=1, 0, cand[1]);
}

\\add labels to a sorted list of ideals
\\assumption: for all I in the list,
\\all the ideals J such that N(I)=N(J) and J<I are also in the list,
\\and all ideals in the list are distinct.
\\flag=1: only return the list of labels
addlabels(nf,L,flag=0) =
{
 my(N=0,a,lab=0,Na,L2);
 if(flag,L2 = [1..#L]);
 for(i=1,#L,
   a = L[i];
   Na = idealnorm(nf,a);
   if(Na==N,
     lab += 1,
   \\else
     lab = 1;
     N = Na);
   if(flag,
     L2[i] = [N,lab],
   \\else
     L[i] = [[N,lab],a]);
 );
 if(flag,L2,L);
}

\\sorted prime ideals above p
try_idealprimedecsorted(nf,p,r,dec) =
{
 my(facto,ha,L = [0 | pr <- dec], pp, x = variable(nf.pol),perm);
 facto = factorpadic(nf.pol,p,r);
 facto = facto[,1]~;
 if(#facto!=#dec, error("Wrong number of primes or factors!",facto,"\n",dec));
 for(i=1,#facto,
  ha = subst(lift(facto[i]), x, Mod(x,nf.pol));
  pp = nfprimematch(nf,ha,p,r,dec);
  if(!pp, return(0));
  L[i] = pp
 );
 \\print(L);
 perm = sortpadic(facto, p, r, [[pp.f,pp.e] | pp <- L]);
 if(perm,[L[perm[i]] | i<-[1..#L]],0);
}
idealprimedecsorted(nf,p) =
{
 my(dec=idealprimedec(nf,p),r=10,res=0);
 while(!res,
  res = try_idealprimedecsorted(nf,p,r,dec);
  r *= 3
 );
 res;
}

\\sorted prime ideals up to norm X
nfprimesupto(nf,x) =
{
  my(Lp,Llab,perm);
  Lp = primes([0,x]);
  Lp = [idealprimedecsorted(nf,p) | p<-Lp];
  Lp = [[pr | pr<-dec, idealnorm(nf,pr)<=x] | dec<-Lp];
  Llab = [addlabels(nf,dec) | dec<-Lp];
  Lp = concat(Lp);
  Llab = concat(Llab);
  perm = vecsort(Llab,,1);
  [Lp[perm[i]] | i <- [1..#perm]];
}

\\nextprimepower (including n, like nextprime)
\\(could use congruence conditions)
nextprimepower(n) =
{
  while(!ispseudoprimepower(n),n++);n;
}

\\nextprimeideal (different from pp)
nextprimeideal(nf,pp) =
{
  my(p=pp.p,dec=idealprimedecsorted(nf,p),i=1,q,f,facto);
  while(dec[i]!=pp, i++);
  if(i<#dec && dec[i+1].f==pp.f, return(dec[i+1]));
  q = p^(pp.f);
  while(1,
    q = nextprimepower(q+1);
    facto = factor(q);
    p = facto[1,1];
    f = facto[1,2];
    dec = idealprimedecsorted(nf,p);
    for(i=1,#dec,
      if(dec[i].f==f, return(dec[i]))
    )
  );
}

idealspowers(nf,L,M) =
{
  my(pow=L, a, pow2);
  for(i=1,#L,
    a = L[i];
    pow2 = [1..M[i]+1];
    for(j=1,M[i],
      pow2[j+1] = idealmul(nf,pow2[j],a)
    );
    pow[i] = pow2;
  );
  pow;
}

\\ fixme === idealfactorback(nf,L)
idealprod(nf,L) =
{
  my(res=1);
  for(i=1,#L,res = idealmul(nf,res,L[i]));
  res;
}
idealmultlist(nf,pows,L) =
{
  my(L2 = [1..#L],expo);
  for(i=1,#L,
    expo = L[i];
    L2[i] = idealprod(nf,[pows[j][expo[j]+1] | j <- [1..#expo]]);
  );
  L2;
}

\\sorted list of ideals of a given prime power norm p^k
idealsprimepowernorm(nf,p,k,dec = idealprimedecsorted(nf,p)) =
{
  my(L,a = [pp.f | pp <- dec],M,pow,keys,L2,perm);
  L = intlinsols(a,k);
  if(!#L,return([]));
  keys = weightrev(L);
  M = maxes(L);
  pow = idealspowers(nf,dec,M);
  L2 = idealmultlist(nf,pow,L);
  perm = vecsort(keys,,1);
  [L2[perm[i]] | i <- [1..#perm]];
}

\\number of ideals of prime power norm
nbidealsprimepowernorm(nf,p,k,dec = idealprimedec(nf,p)) =
{
  my(a = [pp.f | pp <- dec]);
  nbintlinsols(a,k);
}

\\auxiliary functions
lexallprods(nf,LL) =
{
  my(L,k=#LL);
  if(k==0, return([1]));
  if(#LL[1]==0, return([]));
  L = lexallprods(nf,sublist(LL,2,k));
  L = [[idealmul(nf,a,b) | b <- L] | a <- LL[1]];
  concat(L);
}
finddec(nf,p,Lp,Ldec) =
{
  my(i = vecsearch(Lp,p));
  if(i,
    Ldec[i],
  \\else
    idealprimedecsorted(nf,p)
  );
}

\\sorted list of ideals of a given norm
\\N can be a factorisation matrix
idealsofnorm(nf,N,Lp=[],Ldec=[]) =
{
  my(k, primepow, facto=N);
  if(type(facto)!="t_MAT", facto=factor(N));
  k = #facto[,1];
  primepow = [idealsprimepowernorm(nf,facto[i,1],facto[i,2],finddec(nf,facto[i,1],Lp,Ldec)) | i<-[1..k]];
  lexallprods(nf,primepow);
}

\\sorted ideals up to norm X
\\TODO optimise (forfactored, etc.)
\\ FIXME: === concat(ideallist(nf,x)) up to ordering...
idealsupto(nf,x) =
{
  my(L,N=floor(x),Lp,Ldec);
  Lp = primes([0,N]);
  Ldec = [idealprimedecsorted(nf,p) | p<-Lp];
  L = [1..N];
  for(n=1,N,L[n] = idealsofnorm(nf,n,Lp,Ldec));
  concat(L);
}

\\number of ideals of norm
nbidealsofnorm(nf,N) =
{
  my(facto=N);
  if(type(facto)!="t_MAT", facto=factor(N));
  prod(i=1,#facto[,1], nbidealsprimepowernorm(nf,facto[i,1],facto[i,2]));
}

\\auxiliary function
\\ideal of prime power norm -> label
ppn_ideal2label(nf, x, dec) =
{
  my(n=#dec, w, expo=[1..n], lab, a = [pp.f | pp <- dec], k, b=a);
  for(i=1,n,
    expo[i] = idealval(nf, x, dec[i])
  );
  w = vecsum(expo);
  k = sum(i=1, n, expo[i]*a[i]);
  lab = 1 + vecsum(nbintlinsols2(a,k,w-1,1));
  for(i=1,n-1,
    b = a[i+1..n];
    for(xi=expo[i]+1,min(k\a[i],w),
      lab += nbintlinsols2(b,k-a[i]*xi,w-xi)
    );
    k -= a[i]*expo[i];
    w -= expo[i]
  );
  lab;
}

\\ideal -> label
ideal2label(nf,x) =
{
  my(facto=idealfactor(nf,x),Lp,lab=0,N=idealnorm(nf,x),p,k);
  Lp = facto[,1];
  Lp = [pp.p | pp <- Lp];
  Lp = vecsort(Lp,,8);
  for(i=1,#Lp,
    p = Lp[i];
    dec = idealprimedecsorted(nf,p);
    k = valuation(N,p);
    lab *= nbidealsprimepowernorm(nf,p,k,dec);
    lab += ppn_ideal2label(nf,x,dec)-1
  );
  [N,lab+1];
}

\\auxiliary functions
findweight(lab,sols) =
{
  my(tot=0,k=#sols);
  for(w=1,k,
    if(tot+sols[w]>=lab,
      return([w,tot]),
    \\else
      tot += sols[w])
  );
  [-1,-1];\\should not be reached
}
findxi(lab,tot,b,k,w,ai) =
{
  my(sols);
  forstep(xi=min(k\ai,w),0,-1,
    sols = nbintlinsols2(b,k-ai*xi,w-xi);
    if(tot+sols>=lab,
      return([xi,tot]),
    \\
      tot += sols
    )
  );
  [-1,-1];\\should not be reached
}
\\label -> ideal of prime power norm
ppn_label2ideal(nf,lab,k,dec) =
{
  my(w, sols, a=[pp.f|pp<-dec], tot, n=#dec, xi, expo=[1..n]);
  sols = nbintlinsols2(a,k,k+1,1);
  [w,tot] = findweight(lab,sols);

  for(i=1,n,
    [xi,tot] = findxi(lab,tot,sublist(a,i+1,n),k,w,a[i]);
    expo[i] = xi;
    w -= xi;
    k -= a[i]*xi;
  );
  \\print("check: ", lab==tot+1);
  \\print("expo=", expo);
  idealfactorback(nf,dec,expo);
}

\\label -> ideal
\\first component can be a factorisation matrix
label2ideal(nf,lab) =
{
  my(N=lab[1], res=1, facto=N, k, tot, dec, p);
  if(type(facto)!="t_MAT", facto=factor(N));
  k=#facto[,1];
  lab = lab[2]-1;
  forstep(i=k,1,-1,
    p = facto[i,1];
    e = facto[i,2];
    dec = idealprimedecsorted(nf,p);
    tot = nbidealsprimepowernorm(nf,p,e,dec);
    res = idealmul(nf, res, ppn_label2ideal(nf, (lab%tot)+1, e, dec));
    lab \= tot
  );
  res;
};

\\valid label
isvalidideallabel(nf,N,lab) =
{
  lab>0 && lab <= nbidealsofnorm(nf,N);
};

\\next label
nextideallabel(nf,N,lab) =
{
  if(isvalidideallabel(nf,N,lab+1),return([N,lab+1]));
  N++;
  while(!isvalidideallabel(nf,N,1),N++);
  [N,1]
};

\\nextideal
nextideal(nf,a) =
{
  my(N,lab);
  [N,lab] = ideal2label(nf,a);
  [N,lab] = nextideallabel(nf,N,lab);
  label2ideal(nf,[N,lab])
};

\\given a ideal of nf
\\return matrix of the standard basis of a
\\and its inverse
\\note Col(sum_{i=1}^n a_i*x^i) = [a_n,...,a_1,a_0]~
colrev(v) = vector(#v,i,v[#v-i+1])~;
stdbasis(nf,a=matid(poldegree(nf.pol))) =
{
  my(f=1,n=#a,x,B);
  B = matconcat(vector(n,i,colrev(Col(nfbasistoalg(nf,a[,i]).pol))));
  f = denominator(B);
  B *= f;
  B = mathnf(B);
  B = matconcat(vector(n,i,Col(nfalgtobasis(nf,Pol(colrev(B[,i]))))));
  B /= f;
  [B,B^-1]
};

nfstdlift(nf,x,N,stdB=stdbasis(nf)) =
{
  my([B,Bi]=stdB);
  x = nfalgtobasis(nf,x);
  B*((Bi*x)%N)
};

nfstdunif(nf,pr) =
{
  my(B);
  if(pr.e==1, return(pr.p));
  B = Vec(stdbasis(nf,idealhnf(nf,pr))[1]);
  for(i=1,#B,
    if(nfeltval(nf,B[i],pr)==1, return(B[i]))
  )
};

coprimepart(a,N) =
{
  my(c = gcd(a,N));
  while(c!=1,
    a /= c;
    c = gcd(a,N);
  );
  a
};

stdgenprettier(nf,N,g,stdB=stdbasis(nf)) =
{
  my(v,c,c2,den,a);
  if(!g, return([N,g]));
  a = idealadd(nf,N,g);
  v = Vec(g);

  den = denominator(v);
  v *= den;
  c = coprimepart(v[1],N*den);
  v *= Mod(c,den*N)^-1;
  v = liftall(v);
  den /= coprimepart(den,N);
  v /= den;
  g = Pol(v); 
  if(idealadd(nf,N,g)!=a, error("you changed the ideal!"));
  [N,g]
};

idealstdgen(nf,a,stdB=stdbasis(nf),pretty=1) =
{
  my(N,faN,y,pr,g);
  a = idealhnf(nf,a);
  N = a[1,1];
  faN = idealfactor(nf,N);
  y = vector(#faN[,1],i,
    pr = faN[i,1];
    nfeltpow(nf,nfstdunif(nf,pr),idealval(nf,a,pr))
  );
  g = idealchinese(nf,faN,y);
  g = nfstdlift(nf,g,N,stdB);
  g = liftall(nfbasistoalg(nf,g));
  if(!pretty, return([N,g]));
  stdgenprettier(nf,N,g,stdB)   \\extra code to make the generator look better
                                \\not in the current definition
};

