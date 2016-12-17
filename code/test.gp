read("ideals.gp");

Lpol = [\
  x^2+1,\
  x^2-x-1,\
  x^3-x^2+2*x+8,\
  x^4 - x^3 - 4*x^2 - 3*x + 79,\
  x^5 - 19*x^3 - 35*x^2 + 18*x - 29,\
  x^4 - 8748*x^3 + 24977727*x^2 + 617645502008739*x + 216058595407965,\
  x^10-3*x^9-35*x^8+120*x^7+242*x^6-1080*x^5+44*x^4+2343*x^3-1631*x^2+111*x+79\
];

test1(nf,X) =
{
  my(L,Llab,lab2,a);
  X *= (1+10\poldegree(nf.pol));
  print(" test 1, X=",X);
  L = idealsupto(nf,X);
  Llab = addlabels(nf,L,1);
  for(i=1,#L,
    lab2 = ideal2label(nf,L[i]);
    if(lab2 != Llab[i],
      error("test1:",nf.pol,"\ni=",i,"\nlab=",lab," lab2=",lab2));
    a = label2ideal(nf,Llab[i]);
    if(idealhnf(nf,a) != idealhnf(nf,L[i]),
      error("test1:",nf.pol,"\ni=",i,"\nlab=",lab,"\nideal=",L[i],"\na=",a))
  );
  0
}

test2(nf,X) =
{
  my(nb);
  X *= (1+10\poldegree(nf.pol));
  print(" test 2, X=", X);
  for(n=1,X,
    nb = nbidealsofnorm(nf,n);
    for(i=1,nb,
      if(ideal2label(nf,label2ideal(nf,[n,i]))!=[n,i],
      error("test2:",nf.pol,"\nlab=",[n,i]))
    )
  );
  0
}

test3(nf,X,k) =
{
  my(nb,n,i,try);
  k *= (1+9\poldegree(nf.pol));
  print(" test 3, X=", X, " k=", k);
  for(j=1,k,
    nb = 0;
    try=0;
    while(!nb,
      try++;
      \\if(try%500==0, print(try));
      n = random([1,X]);
      nb = nbidealsofnorm(nf,n));
    i = random([1,nb]);
    if(ideal2label(nf,label2ideal(nf,[n,i]))!=[n,i],
      error("test3:",nf.pol,"\nlab=",[n,i]))
  );
  0
}

test4(nf,k) =
{
  my(i=0,N=1,nb,lab,p);
  k *= (1+10\poldegree(nf.pol));
  print(" test 4, k=", k);
  p=2;
  while(i<k,
    dec = idealprimedec(nf,p);
    if(#dec>1 && dec[1].f==1 && dec[2].f==1,
      N *= p;
      i++;
      nb = nbidealsofnorm(nf,N);
      lab = random([1,nb]);
      if(ideal2label(nf,label2ideal(nf,[N,lab]))!=[N,lab],
        error("test4:",nf.pol,"\nlab=",[N,lab]))
    );
    p = nextprime(p+1);
  );
  print("  N=", N);
  print("  nb=", nb);
  0
}

runtests(run1=1,run2=1,run3a=1,run3b=1,run4=1) =
{
  for(i=1,#Lpol,
    pol = Lpol[i];
    print("testing ", pol);
    nf = nfinit(pol);
    print("disc=", nf.disc);
    if(run1,test1(nf,2000));
    if(run2,test2(nf,3000));
    if(run3a,test3(nf,10^20,200));
    if(run3b,test3(nf,10^40,5));
    if(run4,test4(nf,50));
  );
  0
}

nfeltformat(nf,x) =
{
  subst(lift(nfbasistoalg(nf,x)), variable(nf.pol), 'a);
}

checkidlab(nf,x,lab) =
{
  my(lab2,y);
  lab2 = ideal2label(nf,x);
  if(lab2!=lab, error("checkidlab1:",nf.pol,"\nx=",x,"\nlab=",lab));
  y = label2ideal(nf,lab);
  y = idealhnf(nf,y);
  x = idealhnf(nf,x);
  if(x!=y, error("checkidlab2:",nf.pol,"\nx=",x,"\nlab=",lab));
  0
}

writeideal(nf,x,filename,lab=ideal2label(nf,x)) =
{
  my(a,b);
  checkidlab(nf,x,lab);
  [a,b] = idealtwoelt(nf,x);
  a = nfeltformat(nf,a);
  b = nfeltformat(nf,b);
  write(filename, lab[1],".",lab[2], " (",a,", ",b,")");
}

dumpideallist(nf, filename, mpr=1000, mid=200, M=20000, k=20) =
{
  my(m,L,Llab,nb,n,i,x,lab);
  write(filename, "# Defining polynomial\n", nf.pol);

  write(filename, "# Primes of norm up to ", mpr);
  L = nfprimesupto(nf,mpr);
  Llab = addlabels(nf,L,1);
  for(i=1,#L,writeideal(nf,L[i],filename,Llab[i]));
  
  write(filename, "# Ideals of norm up to ", mid);
  L = idealsupto(nf,mid);
  Llab = addlabels(nf,L,1);
  for(i=1,#L,writeideal(nf,L[i],filename,Llab[i]));

  write(filename, "# ", k, " random ideals of norm up to ", M);
  for(t=1,k,
    nb=0;
    while(!nb,
      n = random([1,M]);
      nb = nbidealsofnorm(nf,n);
    );
    i = random([1,nb]);
    lab = [n,i];
    x = label2ideal(nf,lab);
    writeideal(nf,x,filename,lab);
  );
  0
}

