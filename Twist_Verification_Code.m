///////////////////////////////////

//README: This code assumes the user already has access to the ell-adic-images code from Andrew Sutherland for CM elliptic curves.
//For each CM discriminant D with order of class number 2
//this code shows that the list of elliptic curves with CM discriminant D and non-maximal ell-adic image
//for some prime ell is the same as the those present in Tables 2 and 4 of our paper.
//For more detail on this method, see Section 4 of our paper, in particular Examples 4.4 and 4.5

///////////////////////////////////

//Takes as input CM elliptic curve E and prime ell
//Returns the CM label for the ell-adic image of E
GL2CMEllAdicLabelFromCurve:=function(E,ell)
	yesno,D:=HasComplexMultiplication(E);
	H:=GL2CMEllAdicImage(E,ell);
	return GL2CMEllAdicLabel(D,H);
end function;

//Takes as input CM label
//Returns label as a tuple with each entry separated
//label ell.nu.c-n.i.t --> <ell, nu, c, n, i, t>
StringToNumbers:=function(label)
  s:=Split(label,".");
  return <StringToInteger(s[1]),StringToInteger(s[2]),Split(s[3],"-")[1], StringToInteger(Split(s[3],"-")[2]),StringToInteger(s[4]),StringToInteger(s[5])>;
end function; 

//Takes as input a discriminant vector [d, f]
//Returns the primes ell for which non-maximal images can occur for CM discriminant D = d*f^2
PrimesOfInterest := function(dfvec)
	d := dfvec[1];
	f := dfvec[2];
	disc := d*f^2;
	if IsOdd(disc) then
		POI := PrimeDivisors(disc);
	else
		disc_wo_2 := disc div 2^Valuation(disc, 2);
		bool_list := [
				d mod 4 eq 1 and f mod 4 eq 0, 
				d mod 4 eq 0 and f mod 2 eq 0, 
				d mod 8 eq 0,
				d mod 8 eq 4 and f mod 4 eq 0,
				d mod 4 eq 1 and f mod 8 eq 0
				];
		if &or bool_list then
			POI := PrimeDivisors(disc);
		else
			POI := PrimeDivisors(disc_wo_2);
		end if;
	end if;
	return Set(POI);
end function;

//Takes as input a discriminant vector [d, f], base field K, and CM elliptic curve E defined over K
//Returns all twists of E which have non-maximal ell-adic image for some prime ell
Non_Maximal_Twists := function(dfvec, K, E)
    OK := MaximalOrder(K);
	UK, mappy := UnitGroup(OK);
	FundUnits := [mappy(g) : g in Generators(UK)];
    
    N_E := Norm(Conductor(E));
    Disc_K := Discriminant(OK);
    POI := Setseq(PrimesOfInterest(dfvec));

    M := N_E * Disc_K;
    for p in POI do
	    M *:= p;
    end for;
    Fact := Factorization(M*OK);
    gens := [];
    for I in Fact do
        bool, pi := IsPrincipal(I[1]);
        gens := Append(gens, pi);
    end for;

    Divs := [1, gens[1]];
    n := #gens;
    i := 2;
    while i le n do
        Divs := Divs cat [elt*gens[i] : elt in Divs];
        i +:= 1;
    end while;

    PossibleTwists := [k*alpha*u^s : alpha in Divs, k in [1, -1], s in [0, 1], u in FundUnits];

    PossibleTwists := Setseq(Set(PossibleTwists));

    Non_Max_Twists := [];

    for twist in PossibleTwists do
	    Etest := MinimalModel(QuadraticTwist(E, twist));
	    i := 1;
	    len := #POI;
	    test_bool := true;
	    while i le len and test_bool do
		    ell := POI[i];
		    Label := StringToNumbers(GL2CMEllAdicLabelFromCurve(Etest, ell));
		    if Label[5] eq 2 then
			    Non_Max_Twists := Append(Non_Max_Twists, Etest);
			    test_bool := false;
		    else
			    i +:= 1;
		    end if;
	    end while;
    end for;

    return Set(Non_Max_Twists);
end function;

/////////////////////////////
//discriminant -48 = -3 * 4^2
/////////////////////////////
dfvec := [-3,4];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 3);

E := EllipticCurve([a + 1, -a - 1, a + 1, 4*a - 13, 11*a - 21]);

N_E := Norm(Conductor(E));
assert N_E eq 16;

POI := PrimesOfInterest(dfvec);
assert POI eq {2, 3};

E_1 := E;
E_m1 := MinimalModel(QuadraticTwist(E, -1));
E_m2 := MinimalModel(QuadraticTwist(E, -2));
E_2 := MinimalModel(QuadraticTwist(E, 2));

E_2a := MinimalModel(QuadraticTwist(E, 2*a));
E_m2a := MinimalModel(QuadraticTwist(E, -2*a));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m1, E_m2, E_2, E_2a, E_m2a};

assert GL2CMEllAdicLabelFromCurve(E_1, 3) eq "3.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m1, 3) eq "3.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m2, 3) eq "3.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_2, 3) eq "3.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_2a, 2) eq "2.4.ns5-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m2a, 2) eq "2.4.ns5-1.1.1";

/////////////////////////////
//discriminant -75 = -3 * 5^2
/////////////////////////////
dfvec := [-3,5];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 1, 6*a - 48, 109*a - 76]);

N_E := Norm(Conductor(E));
assert N_E eq 3^4 * 5^2;

POI := PrimesOfInterest(dfvec);
assert POI eq {3, 5};

E_am3 := MinimalModel(QuadraticTwist(E, a - 3));
E_3a6 := MinimalModel(QuadraticTwist(E, 3*a + 6));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_am3, E_3a6};

assert GL2CMEllAdicLabelFromCurve(E_am3, 5) eq "5.2.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_3a6, 5) eq "5.2.ns-1.1.1";

/////////////////////////////
//discriminant -147
/////////////////////////////
dfvec := [-3,7];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 5);

E := EllipticCurve([0, -a - 1, 1, 4131*a - 11618, 221331*a - 618025]);

N_E := Norm(Conductor(E));
assert N_E eq 49;

POI := PrimesOfInterest(dfvec);
assert POI eq {3, 7};

E_1 := E;
E_m3 := MinimalModel(QuadraticTwist(E, -3));

E_a1 := MinimalModel(QuadraticTwist(E, a + 1));
E_ma2 := MinimalModel(QuadraticTwist(E, -a + 2));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m3, E_a1, E_ma2};

assert GL2CMEllAdicLabelFromCurve(E_1, 3) eq "3.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m3, 3) eq "3.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_a1, 7) eq "7.2.s-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_ma2, 7) eq "7.2.s-1.1.1";

/////////////////////////////
//discriminant -36 = -4 * 3^2
/////////////////////////////
dfvec := [-4,3];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 3);
FundUnit := a - 2;

E := EllipticCurve([a + 1, a - 1, a, 25*a - 45, 72*a - 127]);

N_E := Norm(Conductor(E));
assert N_E eq 9;

POI := PrimesOfInterest(dfvec);
assert POI eq {3};

E_1 := E;
E_m1 := MinimalModel(QuadraticTwist(E, -1));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m1};

/////////////////////////////
//discriminant = -64 = -4 * 4^2
/////////////////////////////
dfvec := [-4,4];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 2);

E := EllipticCurve([a, 1, 0, 15*a - 22, 46*a - 69]);

N_E := Norm(Conductor(E));
assert N_E eq 32;

POI := PrimesOfInterest(dfvec);
assert POI eq {2};

E_1 := E;
E_m1 := MinimalModel(QuadraticTwist(E, -1));
E_a1 := MinimalModel(QuadraticTwist(E, a + 1));
E_ma1 := MinimalModel(QuadraticTwist(E, -a + 1));
E_a := MinimalModel(QuadraticTwist(E, a));
E_am2 := MinimalModel(QuadraticTwist(E, a - 2));
E_ma := MinimalModel(QuadraticTwist(E, -a));
E_a2 := MinimalModel(QuadraticTwist(E, a + 2));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m1, E_a, E_ma, E_a1, E_ma1, E_a2, E_am2};

/////////////////////////////
//discriminant -100 = -4 * 5^2
/////////////////////////////
dfvec := [-4,5];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 0, 117*a - 556, 3920*a - 3640]);

N_E := Norm(Conductor(E));
assert N_E eq 2^12 * 5^2;

POI := PrimesOfInterest(dfvec);
assert POI eq {5};

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {};

/////////////////////////////
//discriminant -112 = -7 * 4^2
/////////////////////////////
dfvec := [-7,4];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 7);

E := EllipticCurve([1, -1, 1, -270*a - 715, 3223*a + 8527]);

N_E := Norm(Conductor(E));
assert N_E eq 1;

POI := PrimesOfInterest(dfvec);
assert POI eq {2, 7};

E_1 := E;
E_m1 := MinimalModel(QuadraticTwist(E, -1));
E_m2 := MinimalModel(QuadraticTwist(E, -2));
E_2 := MinimalModel(QuadraticTwist(E, 2));
E_2a := MinimalModel(QuadraticTwist(E, 2*a));
E_m2a := MinimalModel(QuadraticTwist(E, -2*a));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m1, E_m2, E_2, E_2a, E_m2a};

assert GL2CMEllAdicLabelFromCurve(E_1, 7) eq "7.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m1, 7) eq "7.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m2, 7) eq "7.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_2, 7) eq "7.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_2a, 2) eq "2.4.s-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m2a, 2) eq "2.4.s-1.1.1";

/////////////////////////////
//discriminant = -32 = -8 * 2^2
/////////////////////////////
dfvec := [-8,2];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 2);

E := EllipticCurve([a, -a - 1, 0, 2*a + 2, -3*a - 5]);

N_E := Norm(Conductor(E));
assert N_E eq 64;

POI := PrimesOfInterest(dfvec);
assert POI eq {2};

E_1 := E;
E_m1 := MinimalModel(QuadraticTwist(E, -1));
E_a1 := MinimalModel(QuadraticTwist(E, a + 1));
E_ma1 := MinimalModel(QuadraticTwist(E, -a + 1));
E_a := MinimalModel(QuadraticTwist(E, a));
E_am2 := MinimalModel(QuadraticTwist(E, a - 2));
E_ma := MinimalModel(QuadraticTwist(E, -a));
E_a2 := MinimalModel(QuadraticTwist(E, a + 2));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m1, E_a, E_ma, E_a1, E_ma1, E_a2, E_am2};

/////////////////////////////
//discriminant -72 = -8 * 3^2
/////////////////////////////
dfvec := [-8,3];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 6);

E := EllipticCurve([a, a + 1, a + 1, 67*a - 161, 458*a - 1122]);

N_E := Norm(Conductor(E));
assert N_E eq 1;

POI := PrimesOfInterest(dfvec);
assert POI eq {2, 3};

E_1 := E;
E_m3 := MinimalModel(QuadraticTwist(E, -3));

E_a2 := MinimalModel(QuadraticTwist(E, a + 2));
E_am2 := MinimalModel(QuadraticTwist(E, a - 2));
E_ma2 := MinimalModel(QuadraticTwist(E, -a + 2));
E_mam2 := MinimalModel(QuadraticTwist(E, -a - 2));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m3, E_a2, E_am2, E_ma2, E_mam2};

assert GL2CMEllAdicLabelFromCurve(E_1, 2) eq "2.3.ns7-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m3, 2) eq "2.3.ns7-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_a2, 3) eq "3.2.s-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_am2, 3) eq "3.2.s-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_ma2, 3) eq "3.2.s-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_mam2, 3) eq "3.2.s-1.1.1";

/////////////////////////////
//discriminant -99
/////////////////////////////
dfvec := [-11,3];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 8);

E := EllipticCurve([0, -a, 1, -435*a - 1030, -7890*a - 18717]);

N_E := Norm(Conductor(E));
assert N_E eq 1;

POI := PrimesOfInterest(dfvec);
assert POI eq {3, 11};

E_1 := E;
E_m3 := MinimalModel(QuadraticTwist(E,-3));

E_m4a13 := MinimalModel(QuadraticTwist(E,-4*a+13));
E_4a9 := MinimalModel(QuadraticTwist(E,4*a+9));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m3, E_m4a13, E_4a9};

assert GL2CMEllAdicLabelFromCurve(E_1, 11) eq "11.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m3, 11) eq "11.1.ns-1.1.1";

assert GL2CMEllAdicLabelFromCurve(E_m4a13, 3) eq "3.2.s-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_4a9, 3) eq "3.2.s-1.1.1";

/////////////////////////////
//discriminant -15
/////////////////////////////
dfvec := [-15,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([1, -1, a, -2*a, a]);

N_E := Norm(Conductor(E));
assert N_E eq 81;

POI := PrimesOfInterest(dfvec);
assert POI eq {3, 5};

E_1 := E;
E_m3 := MinimalModel(QuadraticTwist(E, -3));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m3};

assert GL2CMEllAdicLabelFromCurve(E_1, 5) eq "5.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m3, 5) eq "5.1.ns-1.1.1";

/////////////////////////////
//discriminant -60 = -15 * 2^2
/////////////////////////////
dfvec := [-15,2];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([a, -a - 1, a + 1, -13*a - 14, -20*a - 6]);

N_E := Norm(Conductor(E));
assert N_E eq 81;

POI := PrimesOfInterest(dfvec);
assert POI eq {3, 5};

E_1 := E;
E_m3 := MinimalModel(QuadraticTwist(E, -3));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m3};

assert GL2CMEllAdicLabelFromCurve(E_1, 5) eq "5.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m3, 5) eq "5.1.ns-1.1.1";

/////////////////////////////
//discriminant -20
/////////////////////////////
dfvec := [-20,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, -a, 0, -a - 9, -6*a - 15]);

N_E := Norm(Conductor(E));
assert N_E eq 2^12;

POI := PrimesOfInterest(dfvec);
assert POI eq {5};

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {};

/////////////////////////////
//discriminant = -24
/////////////////////////////
dfvec := [-24,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 2);

E := EllipticCurve([a, 1, 1, a - 3, -a + 1]);
 
N_E := Norm(Conductor(E));
assert N_E eq 81;

POI := PrimesOfInterest(dfvec);
assert POI eq {2,3};

E_1 := E;
E_m3 := MinimalModel(QuadraticTwist(E, -3));

G1 := GL2CMEllAdicImage(E_1, 3);
G2 := GL2CMEllAdicImage(E_m3, 3);

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m3};

assert GL2CMEllAdicLabelFromCurve(E_1, 2) eq "2.3.ns5-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m3, 2) eq "2.3.ns5-1.1.1";

/////////////////////////////
//discriminant -35
/////////////////////////////
dfvec := [-35,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, -1, 1, -14*a + 19, 21*a - 36]);

N_E := Norm(Conductor(E));
assert N_E eq 7^4;

POI := PrimesOfInterest(dfvec);
assert POI eq {5, 7};

E_1 := E;
E_m7 := MinimalModel(QuadraticTwist(E, -7));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m7};

assert GL2CMEllAdicLabelFromCurve(E_1, 5) eq "5.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m7, 5) eq "5.1.ns-1.1.1";

/////////////////////////////
//discriminant -40
/////////////////////////////
dfvec := [-40,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 0, 6*a - 28, 16*a - 56]);

N_E := Norm(Conductor(E));
assert N_E eq 2^16;

POI := PrimesOfInterest(dfvec);
assert POI eq {2, 5};

E_a := MinimalModel(QuadraticTwist(E, a));
E_ma := MinimalModel(QuadraticTwist(E, -a));
E_m2a := MinimalModel(QuadraticTwist(E, -2*a));
E_2a := MinimalModel(QuadraticTwist(E, 2*a));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_a, E_ma, E_m2a, E_2a};

assert GL2CMEllAdicLabelFromCurve(E_a, 5) eq "5.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_ma, 5) eq "5.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m2a, 5) eq "5.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_2a, 5) eq "5.1.ns-1.1.1";

/////////////////////////////
//discriminant -51
/////////////////////////////
dfvec := [-51,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 4);

E := EllipticCurve([0, 0, 1, -6*a - 12, 14*a + 19]);

N_E := Norm(Conductor(E));
assert N_E eq 81;

POI := PrimesOfInterest(dfvec);
assert POI eq {3, 17};

E_1 := E;
E_m3 := MinimalModel(QuadraticTwist(E, -3));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m3};

assert GL2CMEllAdicLabelFromCurve(E_1, 17) eq "17.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m3, 17) eq "17.1.ns-1.1.1";

/////////////////////////////
//discriminant -52
/////////////////////////////
dfvec := [-52,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 3);

E := EllipticCurve([0, 0, 0, 10*a - 35, 40*a - 76]);

N_E := Norm(Conductor(E));
assert N_E eq 2^12;

POI := PrimesOfInterest(dfvec);
assert POI eq {13};

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {};

/////////////////////////////
//discriminant = -88
/////////////////////////////
dfvec := [-88,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - 2);

E := EllipticCurve([a, 1, 1, -193*a - 453, 2233*a + 4008]);

N_E := Norm(Conductor(E));
assert N_E eq 11^4;

POI := PrimesOfInterest(dfvec);
assert POI eq {2, 11};

E_1 := E;
E_m11 := MinimalModel(QuadraticTwist(E, -11));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m11};

assert GL2CMEllAdicLabelFromCurve(E_1, 2) eq "2.3.ns5-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m11, 2) eq "2.3.ns5-1.1.1";

/////////////////////////////
//discriminant -91
/////////////////////////////
dfvec := [-91,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 3);

E := EllipticCurve([0, 0, 1, 84*a - 182, 539*a - 1213]);

N_E := Norm(Conductor(E));
assert N_E eq 7^4;

POI := PrimesOfInterest(dfvec);
assert POI eq {7, 13};

E_1 := E;
E_m7 := MinimalModel(QuadraticTwist(E, -7));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m7};

assert GL2CMEllAdicLabelFromCurve(E_1, 13) eq "13.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m7, 13) eq "13.1.ns-1.1.1";

/////////////////////////////
//discriminant -115
/////////////////////////////
dfvec := [-115,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 1, 46*a - 368, 2645*a - 6216]);

N_E := Norm(Conductor(E));
assert N_E eq 23^4;

POI := PrimesOfInterest(dfvec);
assert POI eq {5, 23};

E_1 := E;
E_m23 := MinimalModel(QuadraticTwist(E, -23));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m23};

assert GL2CMEllAdicLabelFromCurve(E_1, 5) eq "5.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m23, 5) eq "5.1.ns-1.1.1";

/////////////////////////////
//discriminant -123
/////////////////////////////
dfvec := [-123,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 10);

E := EllipticCurve([0, 0, 1, -60*a - 210, 560*a + 1384]);

N_E := Norm(Conductor(E));
assert N_E eq 81;

POI := PrimesOfInterest(dfvec);
assert POI eq {3, 41};

E_1 := E;
E_m3 := MinimalModel(QuadraticTwist(E,-3));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m3};

assert GL2CMEllAdicLabelFromCurve(E_1, 41) eq "41.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m3, 41) eq "41.1.ns-1.1.1";

/////////////////////////////
//discriminant -148
/////////////////////////////
dfvec := [-148,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 9);

E := EllipticCurve([0, 0, 0, 290*a - 1615, 8120*a - 23268]);

N_E := Norm(Conductor(E));
assert N_E eq 2^12;

POI := PrimesOfInterest(dfvec);
assert POI eq {37};

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {};

/////////////////////////////
//discriminant -187
/////////////////////////////
dfvec := [-187,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 4);

E := EllipticCurve([0, 0, 1, 1430*a - 3520, -40898*a + 104090]);

N_E := Norm(Conductor(E));
assert N_E eq 11^4;

POI := PrimesOfInterest(dfvec);
assert POI eq {11, 17};

E_1 := E;
E_m11 := MinimalModel(QuadraticTwist(E, -11));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m11};

assert GL2CMEllAdicLabelFromCurve(E_1, 17) eq "17.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m11, 17) eq "17.1.ns-1.1.1";

/////////////////////////////
//discriminant -232
/////////////////////////////
dfvec := [-232,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 7);

E := EllipticCurve([0, 0, 0, 7280*a - 36310, 960960*a - 2492952]);

N_E := Norm(Conductor(E));
assert N_E eq 2^16;

POI := PrimesOfInterest(dfvec);
assert POI eq {2, 29};

E_1 := E;
E_m1 := MinimalModel(QuadraticTwist(E, -1));
E_m2 := MinimalModel(QuadraticTwist(E, -2));
E_2 := MinimalModel(QuadraticTwist(E, 2));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m1, E_m2, E_2};

assert GL2CMEllAdicLabelFromCurve(E_1, 29) eq "29.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m1, 29) eq "29.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m2, 29) eq "29.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_2, 29) eq "29.1.ns-1.1.1";

/////////////////////////////
//discriminant -235
//Case can be found at bottom of document
/////////////////////////////

/////////////////////////////
//discriminant -267
/////////////////////////////
dfvec := [-267,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 22);

E := EllipticCurve([0, 0, 1, -1590*a - 8580, 92750*a + 359875]);

N_E := Norm(Conductor(E));
assert N_E eq 81;

POI := PrimesOfInterest(dfvec);
assert POI eq {3, 89};

E_1 := E;
E_m3 := MinimalModel(QuadraticTwist(E,-3));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m3};

assert GL2CMEllAdicLabelFromCurve(E_1, 89) eq "89.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m3, 89) eq "89.1.ns-1.1.1";

/////////////////////////////
//discriminant -403
/////////////////////////////
dfvec := [-403,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 3);

E := EllipticCurve([0, 0, 1, 186930*a - 427490, 58571989*a - 135261471]);

N_E := Norm(Conductor(E));
assert N_E eq 31^4;

POI := PrimesOfInterest(dfvec);
assert POI eq {13, 31};

E_1 := E;
E_m31 := MinimalModel(QuadraticTwist(E, -31));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m31};

assert GL2CMEllAdicLabelFromCurve(E_1, 13) eq "13.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m31, 13) eq "13.1.ns-1.1.1";

/////////////////////////////
//discriminant -427
/////////////////////////////
dfvec := [-427,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 15);

E := EllipticCurve([0, 0, 1, 30030*a - 137060, 5787145*a - 25355528]);

N_E := Norm(Conductor(E));
assert N_E eq 7^4;

POI := PrimesOfInterest(dfvec);
assert POI eq {7, 61};

E_1 := E;
E_m7 := MinimalModel(QuadraticTwist(E,-7));

Twists := Non_Maximal_Twists(dfvec, K, E);

assert Twists eq {E_1, E_m7};

assert GL2CMEllAdicLabelFromCurve(E_1, 61) eq "61.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m7, 61) eq "61.1.ns-1.1.1";


print("Computations beyond this point have intensive time and memory requirements");

/////////////////////////////
//discriminant -235
/////////////////////////////

//For this case, we show that if a curve with a non-maximal image exists, 
//It is isomorphic to the base curve E twisted by 1 or -47
//We then show E^1 and E^-47 have non-maximal 47-adic image
dfvec := [-235,1];
P<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^2 - x - 1);

E := EllipticCurve([0, 0, 1, 4136*a - 17578, 324723*a - 962572]);

N_E := Norm(Conductor(E));
assert N_E eq 47^4;

POI := PrimesOfInterest(dfvec);
assert POI eq {5, 47};

E_1 := E;
E_m47 := MinimalModel(QuadraticTwist(E, -47));

OK := MaximalOrder(K);
UK, mappy := UnitGroup(OK);
FundUnits := [mappy(g) : g in Generators(UK)];
    
Disc_K := Discriminant(OK);
POI := Setseq(POI);

M := N_E * Disc_K;
for p in POI do
	M *:= p;
end for;
Fact := Factorization(M*OK);
gens := [];
for I in Fact do
    bool, pi := IsPrincipal(I[1]);
    gens := Append(gens, pi);
end for;

Divs := [1, gens[1]];
n := #gens;
i := 2;
while i le n do
	Divs := Divs cat [elt*gens[i] : elt in Divs];
    i +:= 1;
end while;

PossibleTwists := [k*alpha*u^s : alpha in Divs, k in [1, -1], s in [0, 1], u in FundUnits];
PossibleTwists := Setseq(Set(PossibleTwists));

Non_Max_Twists := [];

for twist in PossibleTwists do
	Etest := MinimalModel(QuadraticTwist(E, twist));
	i := 1;
	len := #POI;
	test_bool := true;
	while i le len and test_bool do
		ell := POI[i];
        if Etest notin {E_1, E_m47} then
		    Label := StringToNumbers(GL2CMEllAdicLabelFromCurve(Etest, ell));
		    if Label[5] eq 2 then
			    Non_Max_Twists := Append(Non_Max_Twists, Etest);
			    test_bool := false;
		    else
			    i +:= 1;
		    end if;
        else
            i +:= 1;
        end if;
	end while;
end for;

assert Set(Non_Max_Twists) eq {};

assert GL2CMEllAdicLabelFromCurve(E_1, 5) eq "5.1.ns-1.1.1";
assert GL2CMEllAdicLabelFromCurve(E_m47, 5) eq "5.1.ns-1.1.1";

//These computations require significant time and memory
assert GL2CMEllAdicLabelFromCurve(E_1, 47) eq "47.1.s-47.2.1";
assert GL2CMEllAdicLabelFromCurve(E_m47, 47) eq "47.1.s-47.2.1";




