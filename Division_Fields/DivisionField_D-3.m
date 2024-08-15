///////////////////////////////////

//README: This code verifies claims about division fields made in Proposition 3.12 of our paper.

///////////////////////////////////

//////////////////////////////////////////////
//    D=-3 (ell=3)
//////////////////////////////////////////////

R<d>:=RationalFunctionField(Rationals());
Qx<x>:=PolynomialRing(R);
E:=EllipticCurve([0,16*d]);

///////////////////////////////////////////////////////////////

PP3:=DivisionPolynomial(E,3); 
assert PP3 eq 3*x^4 + 192*d*x;
PP9:=DivisionPolynomial(E,9);
P9:=Qx!(PP9/(3*PP3));
assert Degree(P9) eq 36;

L9:=Factorization(Evaluate(Polynomial([s : s in Coefficients(P9) | s ne 0]),2^6*d*x));
assert #L9 eq 2;

f9a:=Polynomial([Integers()!s : s in Coefficients(L9[1][1])]);
assert Degree(f9a) eq 3;

K9a,S:=SplittingField(NumberField(f9a)); // x^3 - 3*x + 1
assert Degree(K9a) eq 3;
assert &and[IsSquare(1+4*s) : s in S];
assert &and[IsPower(s,3) : s in S];

f9b:=Polynomial([Integers()!s : s in Coefficients(L9[2][1])]);
K9b := NumberField(f9b);
assert Degree(K9b) eq 9;
K3 := NumberField(Polynomial([-3,0,0,1])); //x^3 - 3

assert IsSubfield(K9a,K9b);
assert IsSubfield(K3,K9b);

K9,S:=SplittingField(K9b); 
assert Degree(K9) eq 18;
assert IsSquare(K9!-3);
assert &and[IsSquare(1+4*s) : s in S];
assert &and[IsPower(s,3) : s in S];
