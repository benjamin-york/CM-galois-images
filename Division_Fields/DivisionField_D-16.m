///////////////////////////////////

//README: This code verifies the computational assertions made in Proposition 3.9 of our paper

///////////////////////////////////

//////////////////////////////////////////////
//    D=-16 (ell=2)
//////////////////////////////////////////////

Qx<x>:=PolynomialRing(Rationals());
E:=EllipticCurve([ -11, 14 ]);

PP4,P4,P2:=DivisionPolynomial(E,4);
L4:=[f[1] : f in Factorization(P4)];

assert {1,2} eq {Squarefree(Integers()!(Roots(g)[1,1]^3-11*Roots(g)[1,1]+14)) : g in L4 | Degree(g) eq 1};

function Cuenta16(g)
  K<a>,S:=SplittingField(NumberField(g));
  assert &and[IsSquare(s^3-11*s+14) : s in S];
  return K;
end function;

assert Degree(L4[3]) eq 4;
K4:=Cuenta16(L4[3]);   //  x^8 - 4*x^6 + 8*x^4 - 4*x^2 + 1
assert IsSquare(K4!2);

S2:=Subfields(K4,2);
assert {Squarefree(Discriminant(s[1])) : s in S2} eq { -2, -1, 2 };

////////////////////////////////////////////////////////////////////////////

PP8,P8,P2:=DivisionPolynomial(E,8);
P8:=Qx!(P8/(2*P4));

L8:=[f[1] : f in Factorization(P8)];
assert #L8 eq 3;

assert Degree(L8[1]) eq 4;
K8a:=Cuenta16(L8[1]);    // x^4 - 4*x^2 + 2
assert Degree(K8a) eq 4;
assert not IsSubfield(K8a,K4);
assert IsSquare(K8a!2);

assert Degree(L8[2]) eq 4;
K8b:=Cuenta16(L8[2]);  // x^8 + 4*x^7 + 4*x^6 + 2*x^4 + 8*x^3 + 12*x^2 + 8*x + 2
assert Degree(K8b) eq 8;
assert not IsIsomorphic(K8b,K4);
assert not IsSubfield(K8a,K8b);
assert IsSquare(K8b!2);

assert Degree(L8[3]) eq 16;
K8c:=Cuenta16(L8[3]);  // x^32 + 16*x^31 + 120*x^30 + 560*x^29 + 1848*x^28 + 4784*x^27 + 11000*x^26 + 25344*x^25 + 59844*x^24 + 133856*x^23 + 260768*x^22 + 419392*x^21 + 534920*x^20 + 513536*x^19 + 332032*x^18 + 93856*x^17 - 43548*x^16 - 22112*x^15 + 61056*x^14 + 77728*x^13 + 20768*x^12 - 18304*x^11 + 320*x^10 + 21440*x^9 + 8240*x^8 - 8256*x^7 - 1888*x^6 + 3584*x^5 + 800*x^4 - 1216*x^3 + 320*x^2 + 8
assert Degree(K8c) eq 32;
assert IsSubfield(K4,K8c);
assert IsSubfield(K8a,K8c);
assert IsSubfield(K8a,K8c);
assert IsSquare(K8c!2);

S2 := Subfields(K8c, 2);
assert {Squarefree(Discriminant(s[1])) : s in S2} eq { -2, -1, 2 };




