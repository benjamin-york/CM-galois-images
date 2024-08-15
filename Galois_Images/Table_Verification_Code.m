///////////////////////////////////

//README: This code assumes the user already has access to the ell-adic-galois-images code from Andrew Sutherland for CM elliptic curves.
//This code verifies that the data present in Tables 2 and 4 of our paper is accurate.

//In particular, let D be a CM discriminant, and let ell be a prime dividing 2*D. 
//Then for each ell-adic image G occuring for elliptic curve E with CM discriminant D
//we confirm that E has image G, and that G has the form and label given in Tables 2 and 4.
//This code suppliments theoretical work used to confirm all images for j-invariants 0, 1728, 
//as there are infinitely many curves with non-maximal image in those cases.

///////////////////////////////////

//takes rational number r and positive integer N > 1
//returns representative of r mod N
//returns error if r has no representative mod N
RepresentativeModN := function(r, N)
	n := Numerator(r) mod N;
	d := Denominator(r) mod N;
	for x in [0..(N-1)] do
		if d*x mod N eq n then
			return x;
		end if;
	end for;
end function;

//Given dfvec = [d,f] and integer n,
//Returns subgroup of Cartan and normalizer of Cartan mod n
CartanSubgroupAndNormalizer:=function(dfvec,n)
	Gn:=GL(2,Integers(n));
	d:=dfvec[1];
	f:=dfvec[2];
	df2:=Integers()!d*f^2;
	if (df2 mod 4) eq 0 or IsOdd(n) then
		delt:=RepresentativeModN(d*f^2/4,n);
		L:=[[a,b,delt*b,a] : a, b in [0..(n-1)] | GCD((a^2-delt*b^2),n) eq 1];
		Cn:=sub<Gn|L>;
		Nn:=sub<Gn|L,[-1,0,0,1]>;
	else
		delt:=RepresentativeModN((d-1)*f^2/4,n);
		L:=[[a+b*f,b,(delt)*b,a] : a, b in [0..(n-1)] | GCD(((a+b*f)*a-delt*b^2),n) eq 1];
		Cn:=sub<Gn|L>;
		Nn:=sub<Gn|L,[-1,0,f,1]>;
	end if;
return Cn, Nn;
end function;

//Takes as input CM curve E and prime ell
//Returns the CM label for the ell-adic image of E
GL2CMEllAdicLabelFromCurve:=function(E,ell)
	yesno,D:=HasComplexMultiplication(E);
	H:=GL2CMEllAdicImage(E,ell);
	return GL2CMEllAdicLabel(D,H);
end function;


/////////////////////////////
//discriminant -3, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-3,1];

E := EllipticCurve([0, 16]);

E_1 := E;
E_4 := EllipticCurve([0,16*4]);

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "2.0.ns5-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_4,ell) eq "2.0.ns5-2.3.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec, ell^4);

Cell_3 := [g^3 : g in Cell];
c1p := [0, 1, 1, 0];

G_3 := sub<Nell | Cell_3, c1p>;

G_1 := GL2CMEllAdicImage(E_1,ell);
G_4 := GL2CMEllAdicImage(E_4,ell);

assert IsConjugate(GLell,Nell,G_1);
assert IsConjugate(GLell,G_3,G_4);

/////////////////////////////
//discriminant -12, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-3,2];

E := EllipticCurve([-15, 22]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.2.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec, ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -27, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-3,3];

E := EllipticCurve([-480, 4048]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec, ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -48, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-3,4];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 3);

E := EllipticCurve([a + 1, -a - 1, a + 1, 4*a - 13, 11*a - 21]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_m1 := QuadraticTwist(E,-1);
E_2 := QuadraticTwist(E,2);
E_m2 := QuadraticTwist(E,-2);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "2.4.ns5-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_m2,ell) eq "2.4.ns5-8.2.1";
assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "2.4.ns5-8.2.2";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "2.4.ns5-8.2.3";
assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "2.4.ns5-8.2.4";

G_5 := GL2CMEllAdicImage(E_5,ell);

G_1 := GL2CMEllAdicImage(E_1,ell);
G_m1 := GL2CMEllAdicImage(E_m1,ell);
G_2 := GL2CMEllAdicImage(E_2,ell);
G_m2 := GL2CMEllAdicImage(E_m2,ell);

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);

delta := -12;

G21dpList := [[5, 0, 0, 5], [1, 1, delta, 1]];
G22dpList := [[5, 0, 0, 5], [-1, -1, -delta, -1]];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21dp1 := sub<Nell | G21dpList, c1>;
G21dpm1 := sub<Nell | G21dpList, cm1>;
G22dp1 := sub<Nell | G22dpList, c1>;
G22dpm1 := sub<Nell | G22dpList, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21dp1, G_m2);
assert IsConjugate(GLell, G22dp1, G_m1);
assert IsConjugate(GLell, G22dpm1, G_1);
assert IsConjugate(GLell, G21dpm1, G_2);

/////////////////////////////
//discriminant -75, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-3,5];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 1, 6*a - 48, 109*a - 76]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -147, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-3,7];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 5);

E := EllipticCurve([0, -a - 1, 1, 4131*a - 11618, 221331*a - 618025]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -4, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-4,1];

E := EllipticCurve([1, 0]);

E_3 := EllipticCurve([3, 0]);

E_t2 := EllipticCurve([3^2, 0]);
E_mt2 := EllipticCurve([-3^2, 0]);
E_2t2 := EllipticCurve([2*3^2, 0]);
E_m2t2 := EllipticCurve([-2*3^2, 0]);

E_4 := EllipticCurve([4, 0]);
E_1 := E;
E_m4 := EllipticCurve([-4, 0]);
E_m1 := EllipticCurve([-1, 0]);

E_2 := EllipticCurve([2, 0]);
E_8 := EllipticCurve([8, 0]);
E_m8 := EllipticCurve([-8, 0]);
E_m2 := EllipticCurve([-2, 0]);

assert GL2CMEllAdicLabelFromCurve(E_3,ell) eq "2.2.ns7-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_t2,ell) eq "2.2.ns7-4.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mt2,ell) eq "2.2.ns7-4.2.2";
assert GL2CMEllAdicLabelFromCurve(E_2t2,ell) eq "2.2.ns7-8.2.1";
assert GL2CMEllAdicLabelFromCurve(E_m2t2,ell) eq "2.2.ns7-8.2.2";

assert GL2CMEllAdicLabelFromCurve(E_4,ell) eq "2.2.ns7-4.4.1";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "2.2.ns7-4.4.2";
assert GL2CMEllAdicLabelFromCurve(E_m4,ell) eq "2.2.ns7-4.4.3";
assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "2.2.ns7-4.4.4";

assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "2.2.ns7-16.4.1";
assert GL2CMEllAdicLabelFromCurve(E_8,ell) eq "2.2.ns7-16.4.2";
assert GL2CMEllAdicLabelFromCurve(E_m8,ell) eq "2.2.ns7-16.4.3";
assert GL2CMEllAdicLabelFromCurve(E_m2,ell) eq "2.2.ns7-16.4.4";

G21d0List := [ [-1,0,0,-1], [3,0,0,3], [1,2,-2,1] ];
G22d0List := [ [-1,0,0,-1], [3,0,0,3], [2,1,-1,2] ];
G41d0List := [ [5,0,0,5], [1,2,-2,1] ];
G42d0List := [ [5,0,0,5], [-1,-2,2,-1] ];
G43d0List := [ [-3,0,0,-3], [2,-1,1,2] ];
G44d0List := [ [-3,0,0,-3], [-2,1,-1,-2] ];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];
c1p := [0,1,1,0];
cm1p := [0,-1,-1,0];

G_3 := GL2CMEllAdicImage(E_3,ell);

G_t2 := GL2CMEllAdicImage(E_t2,ell);
G_mt2 := GL2CMEllAdicImage(E_mt2,ell);
G_2t2 := GL2CMEllAdicImage(E_2t2,ell);
G_m2t2 := GL2CMEllAdicImage(E_m2t2,ell);

G_4 := GL2CMEllAdicImage(E_4,ell);
G_1 := GL2CMEllAdicImage(E_1,ell);
G_m4 := GL2CMEllAdicImage(E_m4,ell);
G_m1 := GL2CMEllAdicImage(E_m1,ell);

G_2 := GL2CMEllAdicImage(E_2,ell);
G_8 := GL2CMEllAdicImage(E_8,ell);
G_m8 := GL2CMEllAdicImage(E_m8,ell);
G_m2 := GL2CMEllAdicImage(E_m2,ell);

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec, ell^4);

G21d0_1p := sub<Nell | G21d0List, c1p>;
G21d0_1 := sub<Nell | G21d0List, c1>;
G22d0_1p := sub<Nell | G22d0List, c1p>;
G22d0_1 := sub<Nell | G22d0List, c1>;

G42d0_m1p := sub<Nell | G42d0List, cm1p>;
G41d0_m1p := sub<Nell | G41d0List, cm1p>;
G41d0_m1 := sub<Nell | G41d0List, cm1>;
G42d0_m1 := sub<Nell | G42d0List, cm1>;

G43d0_1p := sub<Nell | G43d0List, c1p>;
G44d0_1p := sub<Nell | G44d0List, c1p>;
G43d0_m1 := sub<Nell | G43d0List, cm1>;
G44d0_m1 := sub<Nell | G44d0List, cm1>;

assert IsConjugate(GLell, G_3, Nell);

assert IsConjugate(GLell, G_t2, G21d0_1p);
assert IsConjugate(GLell, G_mt2, G21d0_1);
assert IsConjugate(GLell, G_2t2, G22d0_1p);
assert IsConjugate(GLell, G_m2t2, G22d0_1);

assert IsConjugate(GLell, G_4, G42d0_m1p);
assert IsConjugate(GLell, G_1, G41d0_m1p);
assert IsConjugate(GLell, G_m4, G41d0_m1);
assert IsConjugate(GLell, G_m1, G42d0_m1);

assert IsConjugate(GLell, G_2, G43d0_1p);
assert IsConjugate(GLell, G_8, G44d0_1p);
assert IsConjugate(GLell, G_m8, G43d0_m1);
assert IsConjugate(GLell, G_m2, G44d0_m1);

/////////////////////////////
//discriminant -16, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-4,2];

E := EllipticCurve([-11, 14]);

E_3 := QuadraticTwist(E,3);

E_2 := QuadraticTwist(E,2);
E_1 := E;
E_m1 := QuadraticTwist(E,-1);
E_m2 := QuadraticTwist(E,-2);

assert GL2CMEllAdicLabelFromCurve(E_3,ell) eq "2.4.ns7-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "2.4.ns7-8.2.1";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "2.4.ns7-8.2.2";
assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "2.4.ns7-8.2.3";
assert GL2CMEllAdicLabelFromCurve(E_m2,ell) eq "2.4.ns7-8.2.4";

delta := -4;
G21dpList := [ [5,0,0,5], [1,1,delta,1] ];
G22dpList := [ [5,0,0,5], [-1,-1,-1*delta,-1] ];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G_3 := GL2CMEllAdicImage(E_3,ell);

G_2 := GL2CMEllAdicImage(E_2,ell);
G_1 := GL2CMEllAdicImage(E_1,ell);
G_m1 := GL2CMEllAdicImage(E_m1,ell);
G_m2 := GL2CMEllAdicImage(E_m2,ell);

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec, ell^4);

G21dp_1 := sub<Nell | G21dpList, c1>;
G22dp_1 := sub<Nell | G22dpList, c1>;
G22dp_m1 := sub<Nell | G22dpList, cm1>;
G21dp_m1 := sub<Nell | G21dpList, cm1>;

assert IsConjugate(GLell, G_3, Nell);

assert IsConjugate(GLell, G_2, G21dp_1);
assert IsConjugate(GLell, G_1, G22dp_1);
assert IsConjugate(GLell, G_m1, G22dp_m1);
assert IsConjugate(GLell, G_m2, G21dp_m1);

/////////////////////////////
//discriminant -36, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-4,3];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 3);

E := EllipticCurve([a + 1, a - 1, a, 25*a - 45, 72*a - 127]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.2.ns7-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -64, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-4,4];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 2);

E := EllipticCurve([a, 1, 0, 15*a - 22, 46*a - 69]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_m1 := QuadraticTwist(E, -1);
E_a2 := QuadraticTwist(E, a+2);
E_am2 := QuadraticTwist(E, a-2);
E_a1 := QuadraticTwist(E, a+1);
E_ma1 := QuadraticTwist(E, -a+1);
E_a := QuadraticTwist(E, a);
E_ma := QuadraticTwist(E, -a);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "2.6.ns7-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "2.6.ns7-8.2.1";
assert GL2CMEllAdicLabelFromCurve(E_a,ell) eq "2.6.ns7-8.2.2";
assert GL2CMEllAdicLabelFromCurve(E_ma,ell) eq "2.6.ns7-8.2.3";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "2.6.ns7-8.2.4";

assert GL2CMEllAdicLabelFromCurve(E_am2,ell) eq "2.6.ns7-16.2.1";
assert GL2CMEllAdicLabelFromCurve(E_a1,ell) eq "2.6.ns7-16.2.2";
assert GL2CMEllAdicLabelFromCurve(E_a2,ell) eq "2.6.ns7-16.2.3";
assert GL2CMEllAdicLabelFromCurve(E_ma1,ell) eq "2.6.ns7-16.2.4";

G_5 := GL2CMEllAdicImage(E_5,ell);

G_1 := GL2CMEllAdicImage(E_1,ell);
G_m1 := GL2CMEllAdicImage(E_m1,ell);
G_a2 := GL2CMEllAdicImage(E_a2,ell);
G_am2 := GL2CMEllAdicImage(E_am2,ell);
G_a1 := GL2CMEllAdicImage(E_a1,ell);
G_ma1 := GL2CMEllAdicImage(E_ma1,ell);
G_a := GL2CMEllAdicImage(E_a,ell);
G_ma := GL2CMEllAdicImage(E_ma,ell);

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);

delta := -16;

G21dpList := [[5, 0, 0, 5], [1, 1, delta, 1]];
G22dpList := [[5, 0, 0, 5], [-1, -1, -delta, -1]];
G23dpList := [[3, 0, 0, 3], [1, 1, delta, 1]];
G24dpList := [[3, 0, 0, 3], [-1, -1, -delta, -1]];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21dp_1 := sub<Nell | G21dpList, c1>;
G21dp_m1 := sub<Nell | G21dpList, cm1>;
G22dp_1 := sub<Nell | G22dpList, c1>;
G22dp_m1 := sub<Nell | G22dpList, cm1>;
G_23dp1 := sub<Nell | G23dpList, c1>;
G_23dpm1 := sub<Nell | G23dpList, cm1>;
G_24dp1 := sub<Nell | G24dpList, c1>;
G_24dpm1 := sub<Nell | G24dpList, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21dp_1, G_m1);
assert IsConjugate(GLell, G22dp_1, G_a);
assert IsConjugate(GLell, G22dp_m1, G_ma);
assert IsConjugate(GLell, G21dp_m1, G_1);

assert IsConjugate(GLell, G_23dp1, G_am2);
assert IsConjugate(GLell, G_24dp1, G_a1);
assert IsConjugate(GLell, G_23dpm1, G_a2);
assert IsConjugate(GLell, G_24dpm1, G_ma1);

/////////////////////////////
//discriminant -100, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-4,5];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 0, 117*a - 556, 3920*a - 3640]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.2.ns7-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -7, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-7,1];

E := EllipticCurve([-1715, 33614]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.s-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -28, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-7,2];

E := EllipticCurve([-29155, 1915998]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.2.s-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -112, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-7,4];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 7);

E := EllipticCurve([1, -1, 1, -270*a - 715, 3223*a + 8527]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_m1 := QuadraticTwist(E,-1);
E_2 := QuadraticTwist(E,2);
E_m2 := QuadraticTwist(E,-2);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "2.4.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_m2,ell) eq "2.4.s-8.2.1";
assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "2.4.s-8.2.2";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "2.4.s-8.2.3";
assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "2.4.s-8.2.4";

G_5 := GL2CMEllAdicImage(E_5,ell);

G_1 := GL2CMEllAdicImage(E_1,ell);
G_m1 := GL2CMEllAdicImage(E_m1,ell);
G_2 := GL2CMEllAdicImage(E_2,ell);
G_m2 := GL2CMEllAdicImage(E_m2,ell);

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);

delta := -28;

G21dpList := [[5, 0, 0, 5], [1, 1, delta, 1]];
G22dpList := [[5, 0, 0, 5], [-1, -1, -delta, -1]];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21dp_1 := sub<Nell | G21dpList, c1>;
G21dp_m1 := sub<Nell | G21dpList, cm1>;
G22dp_1 := sub<Nell | G22dpList, c1>;
G22dp_m1 := sub<Nell | G22dpList, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21dp_1, G_m2);
assert IsConjugate(GLell, G22dp_1, G_m1);
assert IsConjugate(GLell, G22dp_m1, G_1);
assert IsConjugate(GLell, G21dp_m1, G_2);

/////////////////////////////
//discriminant -8, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-8,1];

E := EllipticCurve([-4320, 96768]);

E_3 := QuadraticTwist(E,3);

E_2 := QuadraticTwist(E,2);
E_1 := E;
E_m1 := QuadraticTwist(E,-1);
E_m2 := QuadraticTwist(E,-2);

assert GL2CMEllAdicLabelFromCurve(E_3,ell) eq "2.3.ns7-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "2.3.ns7-16.2.1";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "2.3.ns7-16.2.2";
assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "2.3.ns7-16.2.3";
assert GL2CMEllAdicLabelFromCurve(E_m2,ell) eq "2.3.ns7-16.2.4";

delta := -2;
G23d0List := [ [3,0,0,3], [1,1,delta,1] ];
G24d0List := [ [3,0,0,3], [-1,-1,-1*delta,-1] ];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G_3 := GL2CMEllAdicImage(E_3,ell);

G_2 := GL2CMEllAdicImage(E_2,ell);
G_1 := GL2CMEllAdicImage(E_1,ell);
G_m1 := GL2CMEllAdicImage(E_m1,ell);
G_m2 := GL2CMEllAdicImage(E_m2,ell);

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);

G23d0_1 := sub<Nell | G23d0List, c1>;
G24d0_1 := sub<Nell | G24d0List, c1>;
G23d0_m1 := sub<Nell | G23d0List, cm1>;
G24d0_m1 := sub<Nell | G24d0List, cm1>;

assert IsConjugate(GLell, G_3, Nell);

assert IsConjugate(GLell, G_2, G23d0_1);
assert IsConjugate(GLell, G_1, G24d0_1);
assert IsConjugate(GLell, G_m1, G23d0_m1);
assert IsConjugate(GLell, G_m2, G24d0_m1);

/////////////////////////////
//discriminant -32, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-8,2];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 2);

E := EllipticCurve([a, -a - 1, 0, 2*a + 2, -3*a - 5]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_m1 := MinimalModel(QuadraticTwist(E, -1));
E_a2 := MinimalModel(QuadraticTwist(E, a+2));
E_am2 := MinimalModel(QuadraticTwist(E, a-2));
E_a1 := MinimalModel(QuadraticTwist(E, a+1));
E_ma1 := MinimalModel(QuadraticTwist(E, -a+1));
E_a := MinimalModel(QuadraticTwist(E, a));
E_ma := MinimalModel(QuadraticTwist(E, -a));

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "2.5.ns7-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "2.5.ns7-8.2.1";
assert GL2CMEllAdicLabelFromCurve(E_a1,ell) eq "2.5.ns7-8.2.2";
assert GL2CMEllAdicLabelFromCurve(E_ma1,ell) eq "2.5.ns7-8.2.3";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "2.5.ns7-8.2.4";

assert GL2CMEllAdicLabelFromCurve(E_a,ell) eq "2.5.ns7-16.2.1";
assert GL2CMEllAdicLabelFromCurve(E_am2,ell) eq "2.5.ns7-16.2.2";
assert GL2CMEllAdicLabelFromCurve(E_ma,ell) eq "2.5.ns7-16.2.3";
assert GL2CMEllAdicLabelFromCurve(E_a2,ell) eq "2.5.ns7-16.2.4";

G_5 := GL2CMEllAdicImage(E_5,ell);

G_1 := GL2CMEllAdicImage(E_1,ell);
G_m1 := GL2CMEllAdicImage(E_m1,ell);
G_a2 := GL2CMEllAdicImage(E_a2,ell);
G_am2 := GL2CMEllAdicImage(E_am2,ell);

G_a1 := GL2CMEllAdicImage(E_a1,ell);
G_ma1 := GL2CMEllAdicImage(E_ma1,ell);
G_a := GL2CMEllAdicImage(E_a,ell);
G_ma := GL2CMEllAdicImage(E_ma,ell);

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);

delta := -8;

G21dpList := [[5, 0, 0, 5], [1, 1, delta, 1]];
G22dpList := [[5, 0, 0, 5], [-1, -1, -delta, -1]];

G23dpList := [[3, 0, 0, 3], [1, 1, delta, 1]];
G24dpList := [[3, 0, 0, 3], [-1, -1, -delta, -1]];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21dp_1 := sub<Nell | G21dpList, c1>;
G21dp_m1 := sub<Nell | G21dpList, cm1>;
G22dp_1 := sub<Nell | G22dpList, c1>;
G22dp_m1 := sub<Nell | G22dpList, cm1>;

G_23dp1 := sub<Nell | G23dpList, c1>;
G_23dpm1 := sub<Nell | G23dpList, cm1>;
G_24dp1 := sub<Nell | G24dpList, c1>;
G_24dpm1 := sub<Nell | G24dpList, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21dp_1, G_m1);
assert IsConjugate(GLell, G22dp_1, G_a1);
assert IsConjugate(GLell, G22dp_m1, G_ma1);
assert IsConjugate(GLell, G21dp_m1, G_1);

assert IsConjugate(GLell, G_23dp1, G_a);
assert IsConjugate(GLell, G_24dp1, G_am2);
assert IsConjugate(GLell, G_23dpm1, G_ma);
assert IsConjugate(GLell, G_24dpm1, G_a2);

/////////////////////////////
//discriminant -72, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-8,3];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 6);

E := EllipticCurve([a, a + 1, a + 1, 67*a - 161, 458*a - 1122]);

E_1 := E;

E_a2 := QuadraticTwist(E, a + 2);
E_am2 := QuadraticTwist(E, a - 2);
E_ma2 := QuadraticTwist(E, -a + 2);
E_mam2 := QuadraticTwist(E, -a - 2);

assert GL2CMEllAdicLabelFromCurve(E_1, ell) eq "2.3.ns7-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_a2, ell) eq "2.3.ns7-16.2.1";
assert GL2CMEllAdicLabelFromCurve(E_am2, ell) eq "2.3.ns7-16.2.2";
assert GL2CMEllAdicLabelFromCurve(E_ma2, ell) eq "2.3.ns7-16.2.3";
assert GL2CMEllAdicLabelFromCurve(E_mam2, ell) eq "2.3.ns7-16.2.4";

G_1 := GL2CMEllAdicImage(E_1,ell);

G_a2 := GL2CMEllAdicImage(E_a2, ell);
G_am2 := GL2CMEllAdicImage(E_am2, ell);
G_ma2 := GL2CMEllAdicImage(E_ma2, ell);
G_mam2 := GL2CMEllAdicImage(E_mam2, ell);

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);

delta := -18;

G21dpList := [[3, 0, 0, 3], [1, 1, delta, 1]];
G22dpList := [[3, 0, 0, 3], [-1, -1, -delta, -1]];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21dp_1 := sub<Nell | G21dpList, c1>;
G21dp_m1 := sub<Nell | G21dpList, cm1>;
G22dp_1 := sub<Nell | G22dpList, c1>;
G22dp_m1 := sub<Nell | G22dpList, cm1>;

assert IsConjugate(GLell, Nell, G_1);

assert IsConjugate(GLell, G21dp_1, G_a2);
assert IsConjugate(GLell, G22dp_1, G_am2);
assert IsConjugate(GLell, G21dp_m1, G_ma2);
assert IsConjugate(GLell, G22dp_m1, G_mam2);

/////////////////////////////
//discriminant -11, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-11,1];

E := EllipticCurve([-9504, 365904]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -99, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-11,3];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 8);

E := EllipticCurve([0, -a, 1, -435*a - 1030, -7890*a - 18717]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -15, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-15,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([1, -1, a, -2*a, a]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.s-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -60, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-15,2];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([a, -a - 1, a + 1, -13*a - 14, -20*a - 6]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.2.s-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -19, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-19,1];

E := EllipticCurve([-608, 5776]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -20, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-20,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, -a, 0, -a - 9, -6*a - 15]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.2.ns3-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -24, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-24,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 2);

E := EllipticCurve([a, 1, 1, a - 3, -a + 1]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.3.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -35, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-35,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, -1, 1, -14*a + 19, 21*a - 36]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -40, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-40,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 0, 6*a - 28, 16*a - 56]);

E_m3 := QuadraticTwist(E,-3);

E_a := QuadraticTwist(E,a);
E_ma := QuadraticTwist(E, -a);
E_2a := QuadraticTwist(E,2*a);
E_m2a := QuadraticTwist(E,-2*a);

assert GL2CMEllAdicLabelFromCurve(E_m3,ell) eq "2.3.ns3-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_ma,ell) eq "2.3.ns3-16.2.1";
assert GL2CMEllAdicLabelFromCurve(E_m2a,ell) eq "2.3.ns3-16.2.2";
assert GL2CMEllAdicLabelFromCurve(E_2a,ell) eq "2.3.ns3-16.2.3";
assert GL2CMEllAdicLabelFromCurve(E_a,ell) eq "2.3.ns3-16.2.4";

G_m3 := GL2CMEllAdicImage(E_m3,ell);

G_a := GL2CMEllAdicImage(E_a,ell);
G_ma := GL2CMEllAdicImage(E_ma,ell);
G_2a := GL2CMEllAdicImage(E_2a,ell);
G_m2a := GL2CMEllAdicImage(E_m2a,ell);

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);

delta := -10;

G21dpList := [[3, 0, 0, 3], [1, 1, delta, 1]];
G22dpList := [[3, 0, 0, 3], [-1, -1, -delta, -1]];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21dp_1 := sub<Nell | G21dpList, c1>;
G21dp_m1 := sub<Nell | G21dpList, cm1>;
G22dp_1 := sub<Nell | G22dpList, c1>;
G22dp_m1 := sub<Nell | G22dpList, cm1>;

assert IsConjugate(GLell, Nell, G_m3);

assert IsConjugate(GLell, G21dp_1, G_ma);
assert IsConjugate(GLell, G22dp_1, G_m2a);
assert IsConjugate(GLell, G21dp_m1, G_2a);
assert IsConjugate(GLell, G22dp_m1, G_a);

/////////////////////////////
//discriminant -43, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-43,1];

E := EllipticCurve([-13760, 621264]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -51, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-51,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 4);

E := EllipticCurve([0, 0, 1, -6*a - 12, 14*a + 19]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -52, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-52,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 3);

E := EllipticCurve([0, 0, 0, 10*a - 35, 40*a - 76]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.2.ns3-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -67, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-67,1];

E := EllipticCurve([-117920, 15585808]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -88, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-88,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 2);

E := EllipticCurve([a, 1, 1, -193*a - 453, 2233*a + 4008]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.3.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -91, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-91,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 3);

E := EllipticCurve([0, 0, 1, 84*a - 182, 539*a - 1213]); 

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -115, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-115,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 1, 46*a - 368, 2645*a - 6216]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -123, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-123,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 10);

E := EllipticCurve([0, 0, 1, -60*a - 210, 560*a + 1384]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -148, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-148,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 9);

E := EllipticCurve([0, 0, 0, 290*a - 1615, 8120*a - 23268]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.2.ns3-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -163, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-163, 1];

E := EllipticCurve([-34790720, 78984748304]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -187, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-187,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 4);

E := EllipticCurve([0, 0, 1, 1430*a - 3520, -40898*a + 104090]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -232, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-232,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 7);

E := EllipticCurve([0, 0, 0, 7280*a - 36310, 960960*a - 2492952]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_m1 := QuadraticTwist(E,-1);
E_2 := QuadraticTwist(E,2);
E_m2 := QuadraticTwist(E,-2);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "2.3.ns3-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "2.3.ns3-16.2.1";
assert GL2CMEllAdicLabelFromCurve(E_m2,ell) eq "2.3.ns3-16.2.2";
assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "2.3.ns3-16.2.3";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "2.3.ns3-16.2.4";

G_5 := GL2CMEllAdicImage(E_5,ell);

G_1 := GL2CMEllAdicImage(E_1,ell);
G_m1 := GL2CMEllAdicImage(E_m1,ell);
G_2 := GL2CMEllAdicImage(E_2,ell);
G_m2 := GL2CMEllAdicImage(E_m2,ell);

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);

delta := -58;

G21dpList := [[3, 0, 0, 3], [1, 1, delta, 1]];
G22dpList := [[3, 0, 0, 3], [-1, -1, -delta, -1]];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21dp_1 := sub<Nell | G21dpList, c1>;
G21dp_m1 := sub<Nell | G21dpList, cm1>;
G22dp_1 := sub<Nell | G22dpList, c1>;
G22dp_m1 := sub<Nell | G22dpList, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21dp_1, G_m1);
assert IsConjugate(GLell, G22dp_1, G_m2);
assert IsConjugate(GLell, G21dp_m1, G_2);
assert IsConjugate(GLell, G22dp_m1, G_1);

/////////////////////////////
//discriminant -235, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-235,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 1, 4136*a - 17578, 324723*a - 962572]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -267, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-267,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 22);

E := EllipticCurve([0, 0, 1, -1590*a - 8580, 92750*a + 359875]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -403, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-403,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 3);

E := EllipticCurve([0, 0, 1, 186930*a - 427490, 58571989*a - 135261471]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -427, ell = 2
/////////////////////////////
ell := 2;
dfvec := [-427,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 15);

E := EllipticCurve([0, 0, 1, 30030*a - 137060, 5787145*a - 25355528]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "2.0.ns5-1.1.1";

GLell := GL(2,Integers(ell^4));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell^4);
G := GL2CMEllAdicImage(E,ell);

assert IsConjugate(GLell,Nell,G);



/////////////////////////////
//discriminant -3, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-3,1];

E := EllipticCurve([0, 16]);

E_2 := EllipticCurve([0, 16*2]);

E_t2 := EllipticCurve([0, 16*2^2]);
E_m3t2 := EllipticCurve([0, 16*-3*2^2]);

E_t3 := EllipticCurve([0, 16*2^3]);
E_3t3 := EllipticCurve([0, 16*3*2^3]);
E_9t3 := EllipticCurve([0, 16*9*2^3]);

E_1 := E;
E_m27 := EllipticCurve([0, 16*-27]);

E_81 := EllipticCurve([0, 16*81]);
E_9 := EllipticCurve([0, 16*9]);
E_m3 := EllipticCurve([0, 16*-3]);
E_m243 := EllipticCurve([0, 16*-243]);

assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "3.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_t2,ell) eq "3.1.ns-9.2.1";
assert GL2CMEllAdicLabelFromCurve(E_m3t2,ell) eq "3.1.ns-9.2.2";

assert GL2CMEllAdicLabelFromCurve(E_t3,ell) eq "3.1.ns-3.3.1";
assert GL2CMEllAdicLabelFromCurve(E_3t3,ell) eq "3.1.ns-27.3.1";
assert GL2CMEllAdicLabelFromCurve(E_9t3,ell) eq "3.1.ns-27.3.2";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.1.ns-9.6.1";
assert GL2CMEllAdicLabelFromCurve(E_m27,ell) eq "3.1.ns-9.6.2";

assert GL2CMEllAdicLabelFromCurve(E_81,ell) eq "3.1.ns-27.6.1";
assert GL2CMEllAdicLabelFromCurve(E_9,ell) eq "3.1.ns-27.6.2";
assert GL2CMEllAdicLabelFromCurve(E_m3,ell) eq "3.1.ns-27.6.3";
assert GL2CMEllAdicLabelFromCurve(E_m243,ell) eq "3.1.ns-27.6.4";

G_2 := GL2CMEllAdicImage(E_2,ell);

G_t2 := GL2CMEllAdicImage(E_t2,ell);
G_m3t2 := GL2CMEllAdicImage(E_m3t2,ell);

G_t3 := GL2CMEllAdicImage(E_t3,ell);
G_3t3 := GL2CMEllAdicImage(E_3t3,ell);
G_9t3 := GL2CMEllAdicImage(E_9t3,ell);

G_1 := GL2CMEllAdicImage(E_1,ell);
G_m27 := GL2CMEllAdicImage(E_m27,ell);

G_81 := GL2CMEllAdicImage(E_81,ell);
G_9 := GL2CMEllAdicImage(E_9,ell);
G_m3 := GL2CMEllAdicImage(E_m3,ell);
G_m243 := GL2CMEllAdicImage(E_m243,ell);

N := ell^3;
delta := RepresentativeModN(-3/4, N);

G21List := [ [a,b,delta*b,a] : a, b in [0..(N-1)] | (a mod 3) eq 1 ];

G31List := [ [a,b,delta*b,a] : a, b in [0..(N-1)] | ((a mod 3) ne 0) and ((b mod 3) eq 0) ];
G32List := [ [2,0,0,2], [1,1,delta,1] ];
G33List := [ [2,0,0,2], [RepresentativeModN(-5/4, N),RepresentativeModN(1/2, N),RepresentativeModN(-3/8, N),RepresentativeModN(-5/4, N)] ];

G61List := [ [a,b,delta*b,a] : a, b in [0..(N-1)] | ((a mod 3) eq 1) and ((b mod 3) eq 0) ];
G62List := [ [4,0,0,4], [1,1,delta,1] ];
G63List := [ [4,0,0,4], [RepresentativeModN(-5/4, N),RepresentativeModN(1/2, N),RepresentativeModN(-3/8, N),RepresentativeModN(-5/4, N)] ];

c1 := [1, 0, 0, -1];
cm1 := [-1, 0, 0, 1];

GL27 := GL(2,Integers(N));
C27, N27 := CartanSubgroupAndNormalizer(dfvec,N);

G21_1 := sub<N27 | G21List, c1>;
G21_m1 := sub<N27 | G21List, cm1>;

G31_1 := sub<N27 | G31List, c1>;
G32_1 := sub<N27 | G32List, c1>;
G33_1 := sub<N27 | G33List, c1>;

G61_1 := sub<N27 | G61List, c1>;
G61_m1 := sub<N27 | G61List, cm1>;

G62_1 := sub<N27 | G62List, c1>;
G63_1 := sub<N27 | G63List, c1>;
G62_m1 := sub<N27 | G62List, cm1>;
G63_m1 := sub<N27 | G63List, cm1>;

assert IsConjugate(GL27, N27, G_2);

assert IsConjugate(GL27, G21_1, G_t2);
assert IsConjugate(GL27, G21_m1, G_m3t2);

assert IsConjugate(GL27, G31_1, G_t3);
assert IsConjugate(GL27, G32_1, G_3t3);
assert IsConjugate(GL27, G33_1, G_9t3);

assert IsConjugate(GL27, G61_1, G_1);
assert IsConjugate(GL27, G61_m1, G_m27);

assert IsConjugate(GL27, G62_1, G_81);
assert IsConjugate(GL27, G63_1, G_9);
assert IsConjugate(GL27, G62_m1, G_m3);
assert IsConjugate(GL27, G63_m1, G_m243);

/////////////////////////////
//discriminant -12, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-3,2];

E := EllipticCurve([-15, 22]);

E_m1 := QuadraticTwist(E,-1);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "3.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.1.ns-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "3.1.ns-3.2.2";

G_m1 := ChangeRing(GL2CMEllAdicImage(E_m1,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := -3;

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_m1);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -27, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-3,3];

E := EllipticCurve([-480, 4048]);

E_m1 := QuadraticTwist(E,-1);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "3.3.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.3.ns-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "3.3.ns-3.2.2";

G_m1 := ChangeRing(GL2CMEllAdicImage(E_m1,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-27/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_m1);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -48, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-3,4];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 3);

E := EllipticCurve([a + 1, -a - 1, a + 1, 4*a - 13, 11*a - 21]);

E_1 := E;

E_2a := QuadraticTwist(E,2*a);
E_m2a := QuadraticTwist(E,-2*a);

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_2a,ell) eq "3.1.ns-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_m2a,ell) eq "3.1.ns-3.2.2";

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));

G_2a := ChangeRing(GL2CMEllAdicImage(E_2a,ell), Integers(ell));
G_m2a := ChangeRing(GL2CMEllAdicImage(E_m2a,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := -12;

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_1);

assert IsConjugate(GLell, G21d0_1, G_2a);
assert IsConjugate(GLell, G21d0_m1, G_m2a);

/////////////////////////////
//discriminant -75, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-3,5];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 1, 6*a - 48, 109*a - 76]);

E_2 := QuadraticTwist(E,2);

E_am3 := QuadraticTwist(E, a - 3);
E_3a6 := QuadraticTwist(E,3*a + 6);

assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "3.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_am3,ell) eq "3.1.ns-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_3a6,ell) eq "3.1.ns-3.2.2";

G_2 := ChangeRing(GL2CMEllAdicImage(E_2,ell), Integers(ell));

G_am3 := ChangeRing(GL2CMEllAdicImage(E_am3,ell), Integers(ell));
G_3a6 := ChangeRing(GL2CMEllAdicImage(E_3a6,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-75/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_2);

assert IsConjugate(GLell, G21d0_1, G_am3);
assert IsConjugate(GLell, G21d0_m1, G_3a6);

/////////////////////////////
//discriminant -75, ell = 5
/////////////////////////////
ell := 5;
dfvec := [-3,5];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 1, 6*a - 48, 109*a - 76]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "5.2.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -147, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-3,7];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 5);

E := EllipticCurve([0, -a - 1, 1, 4131*a - 11618, 221331*a - 618025]);

E_1 := E;

E_ma2 := QuadraticTwist(E, -a + 2);
E_a1 := QuadraticTwist(E, a + 1);

assert GL2CMEllAdicLabelFromCurve(E_1, ell) eq "3.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_a1, ell) eq "3.1.ns-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_ma2, ell) eq "3.1.ns-3.2.2";

G_1 := ChangeRing(GL2CMEllAdicImage(E_1, ell), Integers(ell));

G_ma2 := ChangeRing(GL2CMEllAdicImage(E_ma2, ell), Integers(ell));
G_a1 := ChangeRing(GL2CMEllAdicImage(E_a1, ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec, ell);

delta := RepresentativeModN(-147/4, ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_1);

assert IsConjugate(GLell, G21d0_1, G_a1);
assert IsConjugate(GLell, G21d0_m1, G_ma2);

/////////////////////////////
//discriminant -147, ell = 7
/////////////////////////////
ell := 7;
dfvec := [-3,7];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 5);

E := EllipticCurve([0, -a - 1, 1, 4131*a - 11618, 221331*a - 618025]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_mell:= QuadraticTwist(E,-7);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "7.2.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "7.2.s-7.2.1";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "7.2.s-7.2.2";

G_5 := ChangeRing(GL2CMEllAdicImage(E_5,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_m3 := ChangeRing(GL2CMEllAdicImage(E_m3,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-147/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21d0_1, G_m3);
assert IsConjugate(GLell, G21d0_m1, G_1);

/////////////////////////////
//discriminant -36, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-4,3];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 3);

E := EllipticCurve([a + 1, a - 1, a, 25*a - 45, 72*a - 127]);

E_2 := QuadraticTwist(E,2);

E_1 := E;
E_m1 := QuadraticTwist(E,-1);

assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "3.2.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "3.2.ns-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.2.ns-3.2.2";

G_2 := ChangeRing(GL2CMEllAdicImage(E_2,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_m1 := ChangeRing(GL2CMEllAdicImage(E_m1,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := -9;

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_2);

assert IsConjugate(GLell, G21d0_m1, G_1);
assert IsConjugate(GLell, G21d0_1, G_m1);

/////////////////////////////
//discriminant -100, ell = 5
/////////////////////////////
ell := 5;
dfvec := [-4,5];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 0, 117*a - 556, 3920*a - 3640]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "5.2.s-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -7, ell = 7
/////////////////////////////
ell := 7;
dfvec := [-7,1];

E := EllipticCurve([-1715, 33614]);

E_m1 := QuadraticTwist(E,-1);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "7.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "7.1.ns-7.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "7.1.ns-7.2.2";

G_m1 := ChangeRing(GL2CMEllAdicImage(E_m1,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-7/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_m1);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -28, ell = 7
/////////////////////////////
ell := 7;
dfvec := [-7,2];

E := EllipticCurve([-29155, 1915998]);

E_m1 := QuadraticTwist(E,-1);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "7.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "7.1.ns-7.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "7.1.ns-7.2.2";

G_m1 := ChangeRing(GL2CMEllAdicImage(E_m1,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-7,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_m1);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -112, ell = 7
/////////////////////////////
ell := 7;
dfvec := [-7,4];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 7);

E := EllipticCurve([1, -1, 1, -270*a - 715, 3223*a + 8527]);

E_1 := E;

E_2a := QuadraticTwist(E, 2*a);
E_m2a := QuadraticTwist(E, -2*a);

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "7.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_2a,ell) eq "7.1.ns-7.2.1";
assert GL2CMEllAdicLabelFromCurve(E_m2a,ell) eq "7.1.ns-7.2.2";

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));

G_2a := ChangeRing(GL2CMEllAdicImage(E_2a,ell), Integers(ell));
G_m2a := ChangeRing(GL2CMEllAdicImage(E_m2a,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-112/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_1);

assert IsConjugate(GLell, G21d0_1, G_2a);
assert IsConjugate(GLell, G21d0_m1, G_m2a);

/////////////////////////////
//discriminant -72, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-8,3];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 6);

E := EllipticCurve([a, a + 1, a + 1, 67*a - 161, 458*a - 1122]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "3.2.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "3.2.s-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.2.s-3.2.2";

G_5 := ChangeRing(GL2CMEllAdicImage(E_5,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-72/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21d0_1, G_mell);
assert IsConjugate(GLell, G21d0_m1, G_1);

/////////////////////////////
//discriminant -11, ell = 11
/////////////////////////////
ell := 11;
dfvec := [-11,1];

E := EllipticCurve([-9504, 365904]);

E_m1 := QuadraticTwist(E,-1);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "11.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "11.1.ns-11.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "11.1.ns-11.2.2";

G_m1 := ChangeRing(GL2CMEllAdicImage(E_m1,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-11/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_m1);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -99, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-11,3];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 8);

E := EllipticCurve([0, -a, 1, -435*a - 1030, -7890*a - 18717]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "3.2.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "3.2.s-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.2.s-3.2.2";

G_5 := ChangeRing(GL2CMEllAdicImage(E_5,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-99/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21d0_1, G_mell);
assert IsConjugate(GLell, G21d0_m1, G_1);

/////////////////////////////
//discriminant -99, ell = 11
/////////////////////////////
ell := 11;
dfvec := [-11,3];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 8);

E := EllipticCurve([0, -a, 1, -435*a - 1030, -7890*a - 18717]);

E_1 := E;

E_m4a13 := QuadraticTwist(E,-4*a+13);
E_4a9 := QuadraticTwist(E,4*a+9);

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "11.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_m4a13,ell) eq "11.1.ns-11.2.1";
assert GL2CMEllAdicLabelFromCurve(E_4a9,ell) eq "11.1.ns-11.2.2";

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));

G_m4a13 := ChangeRing(GL2CMEllAdicImage(E_m4a13,ell), Integers(ell));
G_4a9 := ChangeRing(GL2CMEllAdicImage(E_4a9,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-99/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_1);

assert IsConjugate(GLell, G21d0_1, G_m4a13);
assert IsConjugate(GLell, G21d0_m1, G_4a9);

/////////////////////////////
//discriminant -15, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-15,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([1, -1, a, -2*a, a]);

E_2 := QuadraticTwist(E,2);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "3.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "3.1.s-3.2.2";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.1.s-3.2.1";

G_2 := ChangeRing(GL2CMEllAdicImage(E_2,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-15/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_2);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -15, ell = 5
/////////////////////////////
ell := 5;
dfvec := [-15,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([1, -1, a, -2*a, a]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "5.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -60, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-15,2];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([a, -a - 1, a + 1, -13*a - 14, -20*a - 6]);

E_2 := QuadraticTwist(E,2);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "3.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.1.s-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "3.1.s-3.2.2";

G_2 := ChangeRing(GL2CMEllAdicImage(E_2,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-60/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_2);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -60, ell = 5
/////////////////////////////
ell := 5;
dfvec := [-15,2];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([a, -a - 1, a + 1, -13*a - 14, -20*a - 6]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "5.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -19, ell = 19
/////////////////////////////
ell := 19;
dfvec := [-19,1];

E := EllipticCurve([-608, 5776]);
E_m1 := QuadraticTwist(E,-1);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "19.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "19.1.ns-19.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "19.1.ns-19.2.2";

G_m1 := ChangeRing(GL2CMEllAdicImage(E_m1,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec, ell);

delta := RepresentativeModN(-19/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_m1);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -20, ell = 5
/////////////////////////////
ell := 5;
dfvec := [-20,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, -a, 0, -a - 9, -6*a - 15]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "5.1.s-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -24, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-24,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 2);

E := EllipticCurve([a, 1, 1, a - 3, -a + 1]);

E_m1 := QuadraticTwist(E,-1);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "3.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.1.s-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "3.1.s-3.2.2";

G_m1 := ChangeRing(GL2CMEllAdicImage(E_m1,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-6,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_m1);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -35, ell = 5
/////////////////////////////
ell := 5;
dfvec := [-35,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, -1, 1, -14*a + 19, 21*a - 36]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "5.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -35, ell = 7
/////////////////////////////
ell := 7;
dfvec := [-35,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, -1, 1, -14*a + 19, 21*a - 36]);

E_2 := QuadraticTwist(E,2);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "7.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "7.1.s-7.2.1";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "7.1.s-7.2.2";

G_2 := ChangeRing(GL2CMEllAdicImage(E_2,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-35/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_2);

assert IsConjugate(GLell, G21d0_1, G_mell);
assert IsConjugate(GLell, G21d0_m1, G_1);

/////////////////////////////
//discriminant -40, ell = 5
/////////////////////////////
ell := 5;
dfvec := [-40,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 0, 6*a - 28, 16*a - 56]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "5.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//This case can be found at the bottom of the document
//discriminant -43, ell = 43
/////////////////////////////

/////////////////////////////
//discriminant -51, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-51,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 4);

E := EllipticCurve([0, 0, 1, -6*a - 12, 14*a + 19]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "3.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.1.s-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "3.1.s-3.2.2";

G_5 := ChangeRing(GL2CMEllAdicImage(E_5,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-51/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -51, ell = 17
/////////////////////////////
ell := 17;
dfvec := [-51,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 4);

E := EllipticCurve([0, 0, 1, -6*a - 12, 14*a + 19]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "17.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -52, ell = 13
/////////////////////////////
ell := 13;
dfvec := [-52,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 3);

E := EllipticCurve([0, 0, 0, 10*a - 35, 40*a - 76]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "13.1.s-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//This case can be found at the bottom of the document
//discriminant -67, ell = 67
/////////////////////////////

/////////////////////////////
//discriminant -88, ell = 11
/////////////////////////////
ell := 11;
dfvec := [-88,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 2);

E := EllipticCurve([a, 1, 1, -193*a - 453, 2233*a + 4008]);

E_m1 := QuadraticTwist(E,-1);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_m1,ell) eq "11.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "11.1.s-11.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "11.1.s-11.2.2";

G_m1 := ChangeRing(GL2CMEllAdicImage(E_m1,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-22,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_m1);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -91, ell = 7
/////////////////////////////
ell := 7;
dfvec := [-91,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 3);

E := EllipticCurve([0, 0, 1, 84*a - 182, 539*a - 1213]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "7.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "7.1.s-7.2.1";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "7.1.s-7.2.2";

G_5 := ChangeRing(GL2CMEllAdicImage(E_5,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-91/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21d0_1, G_mell);
assert IsConjugate(GLell, G21d0_m1, G_1);

/////////////////////////////
//discriminant -91, ell = 13
/////////////////////////////
ell := 13;
dfvec := [-91,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 3);

E := EllipticCurve([0, 0, 1, 84*a - 182, 539*a - 1213]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "13.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -115, ell = 5
/////////////////////////////
ell := 5;
dfvec := [-115,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 1, 46*a - 368, 2645*a - 6216]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "5.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -115, ell = 23
/////////////////////////////
ell := 23;
dfvec := [-115,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 1, 46*a - 368, 2645*a - 6216]);

E_2 := QuadraticTwist(E,2);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_2,ell) eq "23.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "23.1.s-23.2.1";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "23.1.s-23.2.2";

G_2 := ChangeRing(GL2CMEllAdicImage(E_2,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-115/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_2);

assert IsConjugate(GLell, G21d0_1, G_mell);
assert IsConjugate(GLell, G21d0_m1, G_1);

/////////////////////////////
//discriminant -123, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-123,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 10);

E := EllipticCurve([0, 0, 1, -60*a - 210, 560*a + 1384]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "3.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.1.s-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "3.1.s-3.2.2";

G_5 := ChangeRing(GL2CMEllAdicImage(E_5,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-123/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -123, ell = 41
/////////////////////////////
ell := 41;
dfvec := [-123,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 10);

E := EllipticCurve([0, 0, 1, -60*a - 210, 560*a + 1384]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "41.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -148, ell = 37
/////////////////////////////
ell := 37;
dfvec := [-148,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 9);

E := EllipticCurve([0, 0, 0, 290*a - 1615, 8120*a - 23268]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "37.1.s-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//This case can be found at the bottom of the document
//discriminant -163, ell = 163
/////////////////////////////

/////////////////////////////
//discriminant -187, ell = 11
/////////////////////////////
ell := 11;
dfvec := [-187,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 4);

E := EllipticCurve([0, 0, 1, 1430*a - 3520, -40898*a + 104090]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "11.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "11.1.s-11.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "11.1.s-11.2.2";

G_5 := ChangeRing(GL2CMEllAdicImage(E_5,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-187/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -187, ell = 17
/////////////////////////////
ell := 17;
dfvec := [-187,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 4);

E := EllipticCurve([0, 0, 1, 1430*a - 3520, -40898*a + 104090]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "17.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -232, ell = 29
/////////////////////////////
ell := 29;
dfvec := [-232,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 7);

E := EllipticCurve([0, 0, 0, 7280*a - 36310, 960960*a - 2492952]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "29.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -235, ell = 5
/////////////////////////////
ell := 5;
dfvec := [-235,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 1, 4136*a - 17578, 324723*a - 962572]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "5.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//This case can be found at the bottom of the document
//discriminant -235, ell = 47
/////////////////////////////

/////////////////////////////
//discriminant -267, ell = 3
/////////////////////////////
ell := 3;
dfvec := [-267,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 22);

E := EllipticCurve([0, 0, 1, -1590*a - 8580, 92750*a + 359875]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "3.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "3.1.s-3.2.1";
assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "3.1.s-3.2.2";

G_5 := ChangeRing(GL2CMEllAdicImage(E_5,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-267/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -267, ell = 89
/////////////////////////////
ell := 89;
dfvec := [-267,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 22);

E := EllipticCurve([0, 0, 1, -1590*a - 8580, 92750*a + 359875]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "89.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -403, ell = 13
/////////////////////////////
ell := 13;
dfvec := [-403,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 3);

E := EllipticCurve([0, 0, 1, 186930*a - 427490, 58571989*a - 135261471]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "13.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);

/////////////////////////////
//discriminant -403, ell = 31
/////////////////////////////
ell := 31;
dfvec := [-403,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 3);

E := EllipticCurve([0, 0, 1, 186930*a - 427490, 58571989*a - 135261471]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "31.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "31.1.s-31.2.1";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "31.1.s-31.2.2";

G_5 := ChangeRing(GL2CMEllAdicImage(E_5,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-403/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21d0_1, G_mell);
assert IsConjugate(GLell, G21d0_m1, G_1);

/////////////////////////////
//discriminant -427, ell = 7
/////////////////////////////
ell := 7;
dfvec := [-427,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 15);

E := EllipticCurve([0, 0, 1, 30030*a - 137060, 5787145*a - 25355528]);

E_5 := QuadraticTwist(E,5);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

assert GL2CMEllAdicLabelFromCurve(E_5,ell) eq "7.1.s-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_mell,ell) eq "7.1.s-7.2.1";
assert GL2CMEllAdicLabelFromCurve(E_1,ell) eq "7.1.s-7.2.2";

G_5 := ChangeRing(GL2CMEllAdicImage(E_5,ell), Integers(ell));

G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-427/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_5);

assert IsConjugate(GLell, G21d0_1, G_mell);
assert IsConjugate(GLell, G21d0_m1, G_1);

/////////////////////////////
//discriminant -427, ell = 61
/////////////////////////////
ell := 61;
dfvec := [-427,1];

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 15);

E := EllipticCurve([0, 0, 1, 30030*a - 137060, 5787145*a - 25355528]);

assert GL2CMEllAdicLabelFromCurve(E,ell) eq "61.1.ns-1.1.1";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);
G := ChangeRing(GL2CMEllAdicImage(E,ell), Integers(ell));

assert IsConjugate(GLell,Nell,G);


print("Computations beyond this point have intensive time and memory requirements");

/////////////////////////////
//discriminant -235, ell = 47
/////////////////////////////
ell := 47;
dfvec := [-235,1];
D := -235;

P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 1, 4136*a - 17578, 324723*a - 962572]);

E_2 := QuadraticTwist(E,2);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

G_2 := ChangeRing(GL2CMEllAdicImage(E_2,ell), Integers(ell));

////////////////////////////////
//These particular computations are time and memory intensive
G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));
////////////////////////////////

assert GL2CMEllAdicLabel(D, G_2) eq "47.1.s-1.1.1";

assert GL2CMEllAdicLabel(D, G_mell) eq "47.1.s-47.2.1";
assert GL2CMEllAdicLabel(D, G_1) eq "47.1.s-47.2.2";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec,ell);

delta := RepresentativeModN(-235/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_2);

assert IsConjugate(GLell, G21d0_1, G_mell);
assert IsConjugate(GLell, G21d0_m1, G_1);

/////////////////////////////
//discriminant -43, ell = 43
/////////////////////////////
ell := 43;
dfvec := [-43,1];
D := -43;

E := EllipticCurve([-13760, 621264]);

E_2 := QuadraticTwist(E,2);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

G_2 := ChangeRing(GL2CMEllAdicImage(E_2,ell), Integers(ell));

////////////////////////////////
//These particular computations are time and memory intensive
G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));
////////////////////////////////

assert GL2CMEllAdicLabel(D, G_2) eq "43.1.ns-1.1.1";

assert GL2CMEllAdicLabel(D, G_mell) eq "43.1.ns-43.2.1";
assert GL2CMEllAdicLabel(D, G_1) eq "43.1.ns-43.2.2";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec, ell);

delta := RepresentativeModN(-43/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_2);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -67, ell = 67
/////////////////////////////
ell := 67;
dfvec := [-67,1];
D := -67;

E := EllipticCurve([-117920, 15585808]);

E_2 := QuadraticTwist(E, 2);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

G_2 := ChangeRing(GL2CMEllAdicImage(E_2,ell), Integers(ell));

////////////////////////////////
//These particular computations are time and memory intensive
G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));
////////////////////////////////

assert GL2CMEllAdicLabel(D, G_2) eq "67.1.ns-1.1.1";

assert GL2CMEllAdicLabel(D, G_mell) eq "67.1.ns-67.2.1";
assert GL2CMEllAdicLabel(D, G_1) eq "67.1.ns-67.2.2";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec, ell);

delta := RepresentativeModN(-67/4, ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_2);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);

/////////////////////////////
//discriminant -163, ell = 163
/////////////////////////////
ell := 163;
dfvec := [-163,1];
D := -163;

E := EllipticCurve([-34790720, 78984748304]);

E_2 := QuadraticTwist(E, 2);

E_1 := E;
E_mell := QuadraticTwist(E,-ell);

G_2 := ChangeRing(GL2CMEllAdicImage(E_2,ell), Integers(ell));

////////////////////////////////
//These particular computations are time and memory intensive
G_1 := ChangeRing(GL2CMEllAdicImage(E_1,ell), Integers(ell));
G_mell := ChangeRing(GL2CMEllAdicImage(E_mell,ell), Integers(ell));
////////////////////////////////

assert GL2CMEllAdicLabel(D, G_2) eq "163.1.ns-1.1.1";

assert GL2CMEllAdicLabel(D, G_mell) eq "163.1.ns-163.2.1";
assert GL2CMEllAdicLabel(D, G_1) eq "163.1.ns-163.2.2";

GLell := GL(2,Integers(ell));
Cell, Nell := CartanSubgroupAndNormalizer(dfvec, ell);

delta := RepresentativeModN(-163/4,ell);

G21d0List := [[a^2,b,delta*b,a^2] : a, b in [0..(ell-1)] | (a mod ell) ne 0];

c1 := [1,0,0,-1];
cm1 := [-1,0,0,1];

G21d0_1 := sub<Nell | G21d0List, c1>;
G21d0_m1 := sub<Nell | G21d0List, cm1>;

assert IsConjugate(GLell, Nell, G_2);

assert IsConjugate(GLell, G21d0_1, G_1);
assert IsConjugate(GLell, G21d0_m1, G_mell);
