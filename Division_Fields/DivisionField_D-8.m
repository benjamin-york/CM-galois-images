///////////////////////////////////

//README: This code verifies claims about division fields made in Proposition 3.6 of our paper.

///////////////////////////////////

//////////////////////////////////////////////
//    D=-8 (ell=2)
//////////////////////////////////////////////

Qx<x> := PolynomialRing(Rationals());
E := EllipticCurve([ -4320, 96768 ]);

function Cuenta8(g)
	K<a>,S:=SplittingField(NumberField(g));
	assert &and[IsSquare(s^3-4320*s+96768) : s in S];
	return K;
end function;

////////////////////////////////////////////////////////////////////////////

PP4,P4,P2:=DivisionPolynomial(E,4);

g2:=[f[1] : f in Factorization(P2) | Degree(f[1]) ne 1][1];

assert 2 eq Squarefree(Discriminant(NumberField(g2)));

////////////////////////////////////////////////////////////////////////////

L4:=[f[1] : f in Factorization(P4)];
assert not 1 in {Degree(g) : g in L4};
assert #L4 eq 2;

K4a<z>,S:=SplittingField(NumberField(L4[1]));  //   x^2 - 2
assert Degree(K4a) eq 2;
assert not &or[IsSquare(s^3-4320*s+96768) : s in S];
assert IsSquare(K4a!2);
assert #S eq 2;
OK4a:=MaximalOrder(K4a);
I2:=Factorization(2*OK4a)[1][1];
boo,alpha2:=IsPrincipal(I2);  //alpha2=Sqrt[2]

Lu:={};
for s in S do
	u:=(s^3-4320*s+96768)/(3^6*2^8*alpha2);
	assert IsUnit(u);	
	assert not IsSquare(u);
	//print(u)
	Lu:=Lu join {u};
end for;

////////////////////////////////

K4b<z>,S:=SplittingField(NumberField(L4[2])); //  x^8 - 4*x^7 + 12*x^6 - 20*x^5 + 24*x^4 - 20*x^3 + 12*x^2 - 4*x + 1
assert Degree(K4b) eq 8;
assert not &or[IsSquare(s^3-4320*s+96768) : s in S];
boo,sqrt2:=IsSquare(K4b!2);

boo,mappy:=IsSubfield(K4a,K4b);
assert &and[IsSquare(mappy(u)) : u in Lu];
assert not IsPower(K4b!2,4);

assert #S eq 4;
OK4b:=MaximalOrder(K4b);
I2:=Factorization(2*OK4b)[1][1];
boo,alpha2:=IsPrincipal(I2);

for s in S do
	u:=(s^3-4320*s+96768)/(3^6*2^8*alpha2^4);
	assert IsUnit(u);
	assert not IsSquare(u); 
	assert IsSquare(u/sqrt2);
	//print MinimalPolynomial(u);
end for;

S2:=Subfields(K4b,2);

assert {Squarefree(Discriminant(s[1])) : s in S2} eq { -2, -1, 2 };

////////////////////////////////////////////////////////////////////////////

PP8,P8,P2:=DivisionPolynomial(E,8);
P8:=Qx!(PP8/(2*PP4));

L8:=[f[1] : f in Factorization(P8)];

assert #L8 eq 2;

assert Degree(L8[1]) eq 8;

K8a:=Cuenta8(L8[1]);    // x^16 - 8*x^15 + 36*x^14 - 104*x^13 + 220*x^12 - 368*x^11 + 516*x^10 - 624*x^9 + 664*x^8 - 624*x^7 + 516*x^6 - 368*x^5 + 220*x^4 - 104*x^3 + 36*x^2 - 8*x + 1
assert Degree(K8a) eq 16;
assert IsSubfield(K4b,K8a);
assert IsSquare(K8a!2);

S2:=Subfields(K8a,2);
assert {Squarefree(Discriminant(s[1])) : s in S2} eq { -2, -1, 2 };

assert Degree(L8[2]) eq 16;

K8b:=Cuenta8(L8[2]); // x^32 + 16*x^31 + 128*x^30 + 672*x^29 + 2544*x^28 + 7200*x^27 + 15352*x^26 + 24272*x^25 + 26904*x^24 + 17312*x^23 - 304*x^22 - 11984*x^21 - 9672*x^20 - 2720*x^19 - 3592*x^18 - 7552*x^17 - 2798*x^16 + 6224*x^15 + 6368*x^14 - 672*x^13 - 2224*x^12 + 3360*x^11 + 4952*x^10 - 1072*x^9 - 4600*x^8 - 1120*x^7 + 1776*x^6 + 752*x^5 - 264*x^4 - 96*x^3 + 24*x^2 + 1
assert Degree(K8b) eq 32;
assert IsSubfield(K8a,K8b);
assert IsPower(K8b!2,4);

S2:=Subfields(K8b,2);
assert {Squarefree(Discriminant(s[1])) : s in S2} eq { -2, -1, 2 };
