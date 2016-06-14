x = polygen(QQ)

Lpol = [\
  x^2+1,\
  x^2-x-1,\
  x^3-x^2+2*x+8,\
  x^4 - x^3 - 4*x^2 - 3*x + 79,\
  x^5 - 19*x^3 - 35*x^2 + 18*x - 29,\
  x^4 - 8748*x^3 + 24977727*x^2 + 617645502008739*x + 216058595407965,\
  x^10-3*x^9-35*x^8+120*x^7+242*x^6-1080*x^5+44*x^4+2343*x^3-1631*x^2+111*x+79\
];

def test1(nf,X):
    X *= (1+10*nf.degree())
    print(" test 1, X={}".format(X))
    for I in ideals_iterator(nf,1,X):
        #print("I = {}".format(I))
        lab = ideal_label(I)
        #print("lab = {}".format(lab))
        J = ideal_from_label(nf,lab);
        #print("J = {}".format(J))
        if I != J:
            print("Error in test1: poly {}, {} --> {} --> {}".format(nf.defining_polynomial(),I,lab,J))

# test2(nf,X) =
# {
#   my(nb);
#   X *= (1+10\poldegree(nf.pol));
#   print(" test 2, X=", X);
#   for(n=1,X,
#     nb = nfnbidealsofnorm(nf,n);
#     for(i=1,nb,
#       if(ideal2label(nf,label2ideal(nf,[n,i]))!=[n,i],
#       error("test2:",nf.pol,"\nlab=",[n,i]))
#     )
#   );
#   0
# }

# test3(nf,X,k) =
# {
#   my(nb,n,i,try);
#   k *= (1+9\poldegree(nf.pol));
#   print(" test 3, X=", X, " k=", k);
#   for(j=1,k,
#     nb = 0;
#     try=0;
#     while(!nb,
#       try++;
#       \\if(try%500==0, print(try));
#       n = random([1,X]);
#       nb = nfnbidealsofnorm(nf,n));
#     i = random([1,nb]);
#     if(ideal2label(nf,label2ideal(nf,[n,i]))!=[n,i],
#       error("test3:",nf.pol,"\nlab=",[n,i]))
#   );
#   0
# }

def runtests():
    for pol in Lpol:
        print("testing {}".format(pol))
        nf = NumberField(pol,'a')
        print("disc = {}".format(nf.disc()))
        test1(nf,2000)
        # test2(nf,3000)
        # test3(nf,10^20,200)
        # test3(nf,10^40,5)


