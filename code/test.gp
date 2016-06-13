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
    nb = nfnbidealsofnorm(nf,n);
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
      nb = nfnbidealsofnorm(nf,n));
    i = random([1,nb]);
    if(ideal2label(nf,label2ideal(nf,[n,i]))!=[n,i],
      error("test3:",nf.pol,"\nlab=",[n,i]))
  );
  0
}

for(i=1,#Lpol,\
  pol = Lpol[i];\
  print("testing ", pol);\
  nf = nfinit(pol);\
  print("disc=", nf.disc);\
  test1(nf,2000);\
  test2(nf,3000);\
  test3(nf,10^20,200);\
  test3(nf,10^40,5)\
);

