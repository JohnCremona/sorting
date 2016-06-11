/* ideals.gp */

\\sort polynomials in Zp[X] of the same degree
\\return 0 if not enough precision
\\o/w return permutation
\\polynomials assumed to be monic and distinct
\\known up to O(p^r)
sortpadic(L,p,r,L2=[[]|i<-[1..#L]]) =
{
 my(perm,k);
 perm = [];
 print(L);
 L = [liftint(Vec(polrecip(P))) | P <- L];
 L = [v[1..#v-1] | v <- L];
 k = -1;
 while(k<r && #perm<#L,
  L2 = [concat(L2[i],L[i]%p) | i <- [1..#L]];
  L \= p;
  perm = vecsort(L2,,1+8);
  k+=1;
  print(k, " ", L2, " ", perm)
 );
 if(k>=r, 0, perm)
}

\\match prime ideals and polynomials
\\ha = h(a), h p-adic factor of minimal polynomial of a
\\return 0 if not enough precision
nfprimematch(nf,ha,p,r,dec=idealprimedec(nf,p)) =
{
 my(cand);
 print("vals: ",[min(nfeltval(nf,ha,pr),(r-1)*pr.e) | pr<-dec]);
 cand = [pr | pr <- dec, nfeltval(nf,ha,pr) >= (r-1)*pr.e];
 if(#cand!=1, 0, cand[1])
}

\\sorted prime ideals above p
try_idealprimedecsorted(nf,p,r,dec) =
{
 my(facto,ha,L = [0 | pr <- dec], pp, x = variable(nf.pol),perm);
 facto = factorpadic(nf.pol,p,r);
 facto = facto[,1]~;
 if(#facto!=#dec, print("error: wrong number of primes or factors!", facto,\
   "\n", dec); return(-1));
 for(i=1,#facto,
  ha = subst(lift(facto[i]), x, Mod(x,nf.pol));
  pp = nfprimematch(nf,ha,p,r,dec);
  if(!pp, return(0));
  L[i] = pp
 );
 perm = sortpadic(facto, p, r, [[pp.f,pp.e] | pp <- L]);
 if(perm,[dec[perm[i]] | i<-[1..#dec]],0)
}
idealprimedecsorted(nf,p) =
{
 my(dec=idealprimedec(nf,p),r=10,res=0);
 while(!res,
  res = try_idealprimedecsorted(nf,p,r,dec);
  r *= 3
 );
 res
}

\\sorted prime ideals up to norm X

\\cmp function for prime power norm ideals

\\sorted prime power norm ideals up to norm X

\\cmp function for ideals

\\sorted ideals up to norm X

\\combinatorics functions
\\...

\\ideal -> label

\\label -> ideal

