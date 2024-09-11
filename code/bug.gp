\r ideals.gp

f = x^4-x^2+4;
K = nfinit(f);
p = 2;
a = Mod(x,K.pol);
P = idealadd(K,p,a);
print(ideal2label(K,P));

f=x^8+6*x^7+21*x^6+56*x^5+123*x^4+224*x^3+336*x^2+384*x+256;
K = nfinit(f);
p = 2;
a = Mod(x,K.pol);
P = idealadd(K,p,2+a+a^2);
print(ideal2label(K,P));
