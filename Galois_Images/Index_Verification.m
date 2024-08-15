///////////////////////////////////

//README: This code assumes the user already has access to the ell-adic-galois-images code from Andrew Sutherland for CM elliptic curves
//This code verifies the claims made in Lemma 3.2, Lemma 3.7, Lemma 3.10, and Lemma 3.13 of our paper

///////////////////////////////////

//Takes as input CM label
//Returns label as a tuple with each entry separated
//label ell.nu.c-n.i.t --> <ell, nu, c, n, i, t>
StringToNumbers:=function(label)
    s:=Split(label,".");
    return <StringToInteger(s[1]),StringToInteger(s[2]),Split(s[3],"-")[1], StringToInteger(Split(s[3],"-")[2]),StringToInteger(s[4]),StringToInteger(s[5])>;
end function; 

//Takes as input CM curve E and prime ell
//Returns the CM label for the ell-adic image of E
GL2CMEllAdicLabelFromCurve:=function(E,ell)
	yesno,D:=HasComplexMultiplication(E);
	H:=GL2CMEllAdicImage(E,ell);
	return GL2CMEllAdicLabel(D,H);
end function;

//takes rational number r and positive integer N > 1
//returns representative of r mod N
//returns error if r has no representative mod N
RepresentativeModN := function(r, N)
	n := Numerator(r) mod N;
	d := Denominator(r) mod N;
	for x in [0..N-1] do
		if d*x mod N eq n then
			return x;
		end if;
	end for;
end function;

//Given dfvec = [d,f] and integer n,
//Returns subgroup of Cartan and normalizer of Cartan
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


/////////////////////////////
//discriminant -4, ell = 2
/////////////////////////////
ell := 2;
n := 8; //level for index of definition
dfvec := [-4,1];
D := -4;

E := EllipticCurve([1,0]);

E_3 := EllipticCurve([3,0]);

E_t2 := EllipticCurve([3^2,0]);
E_mt2 := EllipticCurve([-3^2,0]);
E_2t2 := EllipticCurve([2*3^2,0]);
E_m2t2 := EllipticCurve([-2*3^2,0]);

E_4 := EllipticCurve([4,0]);
E_1 := E;
E_m4 := EllipticCurve([-4,0]);
E_m1 := EllipticCurve([-1,0]);

E_2 := EllipticCurve([2,0]);
E_8 := EllipticCurve([8,0]);
E_m8 := EllipticCurve([-8,0]);
E_m2 := EllipticCurve([-2,0]);

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

Cn, Nn := CartanSubgroupAndNormalizer(dfvec, n);

Curve_List := [E_3, E_t2, E_mt2, E_2t2, E_m2t2, E_4, E_1, E_m4, E_m1, E_2, E_8, E_m8, E_m2];

for Ec in Curve_List do
    G := ChangeRing(GL2CMEllAdicImage(Ec, ell), Integers(n));
    index := #Nn div #G;
    Label := StringToNumbers(GL2CMEllAdicLabel(D, G));
    assert Label[5] eq index;
end for;

/////////////////////////////
//discriminant -8, ell = 2
/////////////////////////////
ell := 2;
n := 8; //level for index of definition
dfvec := [-8,1];
D := -8;

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

Cn, Nn := CartanSubgroupAndNormalizer(dfvec, n);

Curve_List := [E_3, E_1, E_m1, E_2, E_m2];

for Ec in Curve_List do
    G := ChangeRing(GL2CMEllAdicImage(Ec, ell), Integers(n));
    index := #Nn div #G;
    Label := StringToNumbers(GL2CMEllAdicLabel(D, G));
    assert Label[5] eq index;
end for;

/////////////////////////////
//discriminant -16, ell = 2
/////////////////////////////
ell := 2;
n := 8; //level for index of definition
dfvec := [-4,2];
D := -16;

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

Cn, Nn := CartanSubgroupAndNormalizer(dfvec, n);

Curve_List := [E_3, E_1, E_m1, E_2, E_m2];

for Ec in Curve_List do
    G := ChangeRing(GL2CMEllAdicImage(Ec, ell), Integers(n));
    index := #Nn div #G;
    Label := StringToNumbers(GL2CMEllAdicLabel(D, G));
    assert Label[5] eq index;
end for;



/////////////////////////////
//discriminant -3, ell = 3
/////////////////////////////
ell := 3;
n := 9; //level for index of definition
dfvec := [-3,1];
D := -3;

E := EllipticCurve([0,16]);

E_2 := EllipticCurve([0,16*2]);

E_t2 := EllipticCurve([0,16*2^2]);
E_m3t2 := EllipticCurve([0,16*-3*2^2]);

E_t3 := EllipticCurve([0,16*2^3]);
E_3t3 := EllipticCurve([0,16*3*2^3]);
E_9t3 := EllipticCurve([0,16*9*2^3]);

E_1 := E;
E_m27 := EllipticCurve([0,16*-27]);

E_81 := EllipticCurve([0,16*81]);
E_9 := EllipticCurve([0,16*9]);
E_m3 := EllipticCurve([0,16*-3]);
E_m243 := EllipticCurve([0,16*-243]);

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

Cn, Nn := CartanSubgroupAndNormalizer(dfvec, n);

Curve_List := [E_2, E_t2, E_m3t2, E_t3, E_3t3, E_9t3, E_1, E_m27, E_81, E_9, E_m3, E_m243];

for Ec in Curve_List do
    G := ChangeRing(GL2CMEllAdicImage(Ec, ell), Integers(n));
    index := #Nn div #G;
    Label := StringToNumbers(GL2CMEllAdicLabel(D, G));
    assert Label[5] eq index;
end for;

