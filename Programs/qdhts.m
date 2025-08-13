/// Modified code from MAGMA CPS to get an upper bound for all quadratic number fields.
/// A lot of the code has been copied without modification from 'CPSHeightBounds code.rtf'

USE_EXACT := true;

//////////// Non-Archimedean valuations

/// This function has not been modified and computes 
/// The function alpha_v from CPS paper:
function alpha_v(cp,Kod)
if cp eq 1 then return 0; end if;
case Kod:
when KodairaSymbol("I0"):   return 0;
when KodairaSymbol("II"):   return 0;
when KodairaSymbol("III"):  return 1/2;
when KodairaSymbol("IV"):   return 2/3;
when KodairaSymbol("I0*"):  return 1;
when KodairaSymbol("II*"):  return 0;
when KodairaSymbol("III*"): return 3/2;
when KodairaSymbol("IV*"):  return 4/3;
else
n:=0; 
while true do 
n+:=1;
if Kod eq KodairaSymbol("I" cat IntegerToString(n)) 
then // type In
     return (IsEven(n) select n/4 else (n^2-1)/(4*n)); 
else
if Kod eq KodairaSymbol("I" cat IntegerToString(n) cat "*") 
then  // type I*n
      return (cp eq 2 select 1 else (n+4)/4);
end if;
end if;
end while;
end case;
end function;

/// This function has not been modified and computes 
/// The contribution of a non-Archimedean place, when the basefield of the curve is Q

function CPSLocalNonArch_Q(E, P)
/*
intrinsic CPSLocalNonArch(E::CrvEll, P::RngIntElt) -> FldReElt
{Local contribution at P to CPS upper height bound}
require Type(BaseField(E)) eq FldRat : "Base ring of E must be Q";
//require IsMinimalModel(E) : "E must be a minimal model";
require IsPrime(P) : "second argument must be a prime number";
*/
return Log(P) *  alpha_v(localdata[4],localdata[5])
                 where localdata := LocalInformation(E,P);
end function;

/// This function has not been modified and computes 
/// The contribution of a non-Archimedean place, when the basefield of the curve is (here) a quadratic extension

function CPSLocalNonArch_NF(E, P)
/*
intrinsic CPSLocalNonArch(E::CrvEll, P::RngOrdIdl) -> FldReElt
{Local contribution at P to CPS upper height bound}
require Type(BaseField(E)) eq FldNum : "Base ring of E must be a number field";
require IsPrime(P) : "second argument must be a prime ideal";
*/
return (Log(Norm(P))/Degree(BaseField(E))) * 
       (alpha_v(localdata[4],localdata[5]) + 
       (Valuation(Discriminant(E),P)-Valuation(Discriminant(minmodel),P))/6)
where localdata, minmodel := LocalInformation(E,P);
end function;


/// This function computes the smallest non-square module p for a given prime p

function SmallestNonSquare(p)
    e:=1;
    k:=1;
    while k ne -1 do
        e:=e+1;
        k:=KroneckerSymbol(e,p);
    end while;
    return e;
    end function;
        


/// This function computes the maximal possible contribution for places above a fixed prime p, when p is an odd prime
function CPSOddPrimes(E,p)
    e:=SmallestNonSquare(p);
// LB is the list of possible contributions, depending on the place
    LB:=[];
// Contribution if K_v is isomorphic to Q_p
    LB:=Append(LB,2*CPSLocalNonArch_Q(E,p));
// Contribution Q_p(sqrt(n) for n in [p,e*p,e])
    Lp:=[p,e*p,e];
    for n in Lp do
// Generating the corresponding number field
        Kn:=QuadraticField(n);
        En:=BaseChange(E,Kn);
// Generating an ideal above the prime p
        Pn:=Ideal(Decomposition(Kn, p)[1][1]);
// Appending the contribution to the list
        LB:=Append(LB, CPSLocalNonArch_NF(En,Pn));
        end for;
    m1,m2:=Max(LB);
// Return the maximal possible contribution
    return (m1);
    end function;

/// This function computes the maximal possible contribution for places above 2
/// works similarly than the code before

function CPSEvenPrime(E,p)
    L2:=[3,5,-1,2,6,10,-2];
    LB:=[];
    LB:=Append(LB,2*CPSLocalNonArch_Q(E,2));
    for n in L2 do
        Kn:=QuadraticField(n);
        En:=BaseChange(E,Kn);
        Pn:=Ideal(Decomposition(Kn, p)[1][1]);
        LB:=Append(LB, CPSLocalNonArch_NF(En,Pn));
        end for;
    m1,m2:=Max(LB);
    return (m1);
    end function;
    
///////////////////////// Part corresponding to Archimdean valuations


//------------------------------------------
// The following code has been copied without modification
// (end will be indicated again by ----)
// (* only modification was commenting out the vprint, to make the code run)

function de_const(f,g) 
// f,g are real polys;  returns inf_{x\in[-1,1], f(x) ge 0} max{|f(x)|,|g(x)|}
// and sup of same
S := &cat[[r[1] : r in Roots(pol) | IsReal(r[1])] 
          : pol in [g,f+g,f-g,Derivative(f),Derivative(g)]];
S := [x : x in S | -1 le x and x le 1];
S := [x : x in S | Evaluate(f,x) ge 0];
S := [-1,1] cat S;
S := S cat [r[1] : r in Roots(f) | IsReal(r[1]) and -1 le r[1] and r[1] le 1]; 
if #S eq 0 then return []; else
return [Min(T),Max(T)] where T:={Max(Abs(Evaluate(f,x)),Abs(Evaluate(g,x))) : x in S};
end if;
end function;


function CPSReal(E, i)
/*
intrinsic CPSReal(E::CrvEll, i::RngIntElt) -> FldReElt
{Real Archimedean contribution to CPS lower and upper height bounds at i'th real place}
K:=BaseField(E);
require Type(K) eq FldRat or Type(K) eq FldNum: "Base field must be Q or a number field";
*/

    K := BaseField(E);
    bs := bInvariants(E);
    prec := 30;
    numfld := ISA(Type(K), FldNum);
    // print "CPSReal(): initial precision is", prec;
    while true do
    R := RealField(prec);
    if numfld then      // embed in R using i'th embedding of K
        rbs := [ R!Conjugate(b, i : Precision := prec) : b in bs ];
    else
        rbs := ChangeUniverse(bs, R);
    end if;
    b2, b4, b6, b8 := Explode(rbs);
    f := Polynomial([  b6,  2*b4,  b2,     4      ]);
    g := Polynomial([ -b8, -2*b6, -b4,     0,  1  ]);
    F := Polynomial([   0,     4,  b2,  2*b4,  b6 ]);
    G := Polynomial([   1,     0, -b4, -2*b6, -b8 ]);
    de := de_const(f,g);
    dded := de_const(F,G);
    del_recip := (#de eq 0 select dded[2] else Max(de[2], dded[2]));
    eps_recip := (#de eq 0 select dded[1] else Min(de[1], dded[1]));
    if del_recip gt 0 and eps_recip gt 0 then
        del := 1/del_recip;
        eps := 1/eps_recip;
        break;
    end if;

    prec +:= 30;
    // print "increasing precision to", prec;
    end while;

    // "CPSReal returns", [ del, eps ];
    return [ del, eps ];
end function;

// Function to test if the square S=[a,b,r] intersects the closed unit disk
// S=[a,b,r] is the square [a,a+r]x[b,b+r] and is either [-1,-1,2] or contained in one quadrant
function SquareIntersectsDisk(S)
 a,b,r:=Explode(S);
 if r eq 2 then return true; end if; // for the square [-1,-1,2] only 
 a2:=a^2; b2:=b^2; ar2:=(a+r)^2; br2:=(b+r)^2;
 return (a2+b2 le 1) or (ar2+b2 le 1) or (a2+br2 le 1) or (ar2+br2 le 1);
end function;

// Function to test if the square S=[a,b,r] intersects the open unit disk

function SquareIntersectsOpenDisk(S)
 a,b,r:=Explode(S);
 if r eq 2 then return true; end if; // for the square [-1,-1,2] only 
 a2:=a^2; b2:=b^2; ar2:=(a+r)^2; br2:=(b+r)^2;
 allinside:= (a2+b2 lt 1) and (ar2+b2 lt 1) and (a2+br2 lt 1) and (ar2+br2 lt 1);
 alloutside:= (a2+b2 gt 1) and (ar2+b2 gt 1) and (a2+br2 gt 1) and (ar2+br2 gt 1);
 return not (allinside or alloutside);
end function;

// TO DO
// RefineAlphaBound in C 
// (takes all the time in the complex case, which is very slow)

function alphabeta(P,Q); // P,Q complex polynomials
 i:=BaseRing(P).1; 

 function h(z); 
    return Max(Abs(Evaluate(P,z)),Abs(Evaluate(Q,z)));
 end function;

 function E(z,eta); 
    return Max(&+[(eta^n)*Abs(Evaluate(Derivative(P,n),z))/Factorial(n) : n in [1..Degree(P)]],
           &+[(eta^n)*Abs(Evaluate(Derivative(Q,n),z))/Factorial(n) : n in [1..Degree(Q)]]);
 end function;

 RefineAlphaBound:=function (mu,S,al);
  a,b,r:=Explode(S);
  //  "Entering S = ",S," with al=",al, " -- SquareIntersectsDisk(S): ",SquareIntersectsDisk(S);
  if not SquareIntersectsDisk(S) then return al; end if;
  u:=(a+r/2)+(b+r/2)*i;  eta:=r/Sqrt(2);
  if Abs(u) gt 1 then // find a corner of S in D
   eta*:=2; u:=a+b*i;                     // BL corner
    if Abs(u) gt 1 then   u:=(a+r)+b*i;                 // BR corner
     if Abs(u) gt 1 then   u:=a+(b+r)*i;                 // TL corner
      if Abs(u) gt 1 then   u:=(a+r)+(b+r)*i;             // TR corner
       end if;  end if;  end if;   end if;
  // Now u is the centre or a corner of S and is in D
  if Abs(u) gt 1 then "Problem!  u = ",u," is outside the unit circle"; end if;
  //  "u = ",u; "eta = ",eta;
  hu:=h(u);
  if hu-E(u,eta) gt al*Exp(-mu) then return al; end if; // Exp(-mu) here
  if hu lt al then al:=hu; end if;
  al := $$(mu,[a,b,r/2],al);
  al := $$(mu,[a,b+r/2,r/2],al);
  al := $$(mu,[a+r/2,b,r/2],al);
  al := $$(mu,[a+r/2,b+r/2,r/2],al);
  // "Last returning al = ",al;
  return al;
 end function;

 RefineBetaBound:=function (mu,S,be);
  a,b,r:=Explode(S);
  //  "Entering S = ",S," with be=",be, " -- SquareIntersectsDisk(S): ",SquareIntersectsDisk(S);
  if not SquareIntersectsOpenDisk(S) then return be; end if;
  u:=(a+r/2)+(b+r/2)*i;  eta:=r/Sqrt(2);
  if Abs(u) gt 1 then // find a corner of S in D
   eta*:=2; u:=a+b*i;                     // BL corner
   if Abs(u) gt 1 then   u:=(a+r)+b*i;                 // BR corner
    if Abs(u) gt 1 then   u:=a+(b+r)*i;                 // TL corner
     if Abs(u) gt 1 then   u:=(a+r)+(b+r)*i;             // TR corner
      end if;  end if;  end if;   end if;
  // Now u is the centre or a corner of S and is in D
  if Abs(u) gt 1 then "Problem!  u = ",u," is outside the unit circle"; end if;
  //  "u = ",u; "eta = ",eta;
  hu:=h(u);

  if hu-E(u,eta) lt be*Exp(mu) then   return be; end if; // Exp(mu) here
  if hu gt be then  be:=hu; end if;
  be := $$(mu,[a,b,r/2],be);
  be := $$(mu,[a,b+r/2,r/2],be);
  be := $$(mu,[a+r/2,b,r/2],be);
  be := $$(mu,[a+r/2,b+r/2,r/2],be);
  // "Last returning be = ",be;
  return be;
 end function;


  mesh:=10;
  H:=[h((m+n*i)/mesh) : m,n in [-mesh..mesh] | m^2+n^2 le mesh^2];
  al:=Min(H);
  be:=Max(H);
  //"initial alpha = ",al;
  //"initial beta = ",be;
  R:=RealField(Precision(BaseRing(P)));
  mu:=R!0.001;
  al:= RefineAlphaBound(mu,[-1,-1,2],al);
  be:= RefineBetaBound(mu,[-1,-1,2],be);
 // TODO: the user should have control over this initial mu parameter ...
 // "new be = ",be;
 // "final alpha = ",al;
 // "final beta = ",be;
 return [al,be];
end function;

function needed_alphabeta_prec(E, i)
    // Compute needed precision for the alphabeta refinement on E.
    // A precision of 30 is assumed sufficient in order to determine this.
    // The alphabeta refinement works on four polynomials, with coefficients
    //     b6, 2*b4, b2, 4, and  -b8, -2*b6, -b4, 0, 1
    // If mx is the maximum (absolute) value of these cofficients, then we
    // require that mx^12 < 10^prec.  (I don't know why; Mark chose this -- GB)
    // The maximum value will thus be one of  b2, 2*b4, 2*b6, b8, or 4.
    // We do not test 4 as 4^12 < 10^30, and we require prec >= 30.

    p := 30;
    binvs := bInvariants(E);
    b2,b4,b6,b8 := Explode([ Conjugate(b, i : Precision := p) : b in binvs ]);
    mx := Max([ 4, Abs(b2), 2*Abs(b4), 2*Abs(b6), Abs(b8) ]);
    return Max(p, Ceiling(12*Log(10, mx)));
end function;

function alphabeta_exact(OF, OG: Prec := 50)

    B := BaseRing(Parent(OF));
    ES := Eltseq;

    K<i> := QuadraticField(-1);
    P<x,y> := PolynomialRing(K, 2);
    z := x + i*y;

    F := Evaluate(OF, z);
    G := Evaluate(OG, z);

    M := Monomials(F);
    Fe := [ES(c): c in Coefficients(F)];
    P1 := &+[Fe[i, 1]*M[i]: i in [1 .. #M]];
    P2 := &+[Fe[i, 2]*M[i]: i in [1 .. #M]];

    M := Monomials(G);
    Ge := [ES(c): c in Coefficients(G)];
    Q1 := &+[Ge[i, 1]*M[i]: i in [1 .. #M]];
    Q2 := &+[Ge[i, 2]*M[i]: i in [1 .. #M]];

    PQ<x,y> := PolynomialRing(B, 2);
    P1 := PQ!P1;
    P2 := PQ!P2;
    Q1 := PQ!Q1;
    Q2 := PQ!Q2;

    NP := P1^2 + P2^2;
    NQ := Q1^2 + Q2^2;

    dNPdx := Derivative(NP, x);
    dNPdy := Derivative(NP, y);

    dNQdx := Derivative(NQ, x);
    dNQdy := Derivative(NQ, y);

    Ba_i  := [y*dNPdx - x*dNPdy, x^2 + y^2 - 1];
    Ba_ii := [y*dNQdx - x*dNQdy, x^2 + y^2 - 1];
    Bb := [NP - NQ, x^2 + y^2 - 1];
    Bc := [NP - NQ, dNPdx*dNQdy - dNPdy*dNQdx];

    Ia_i  := Ideal(Ba_i);
    Ia_ii := Ideal(Ba_ii);
    Ib := Ideal(Bb);
    Ic := Ideal(Bc);

    IL := [Ia_i, Ia_ii, Ib, Ic];
    //"Ideals:", IL;
//    vprint CPS: "QD:", [QuotientDimension(I): I in IL];

    R := RealField(Prec);
    C<i> := ComplexField(Prec);
    PC<z> := PolynomialRing(C);

    Va := &cat[Variety(I, R): I in [Ia_i, Ia_ii]];
    Va := [t[1] + i*t[2]: t in Va];

    Vb := Variety(Ib, R);
    Vb := [t[1] + i*t[2]: t in Vb];

//    vprint CPS: "V Ia:", Va;
//    vprint CPS: "";
//    vprint CPS: "V Ib:", Vb;
//    vprint CPS: "";

    eps := 0.1;
    Vc := Variety(Ic, R);
    Vc := [t: t in Vc | t[1]^2 + t[2]^2 le 1 + eps];
//    vprint CPS: "V Ic (orig):", Vc;
//   vprint CPS: "";
    Vc := [t[1] + i*t[2]: t in Vc];
//    vprint CPS: "V Ic:", Vc;
//    vprint CPS: "";

    Ma := [Max(Abs(Evaluate(OF, c)), Abs(Evaluate(OG, c))): c in Va];
    Mb := [Max(Abs(Evaluate(OF, c)), Abs(Evaluate(OG, c))): c in Vb];
    Mc := [Max(Abs(Evaluate(OF, c)), Abs(Evaluate(OG, c))): c in Vc];

//    vprint CPS: "Ma norms:", Ma;
//    vprint CPS: "Mb norms:", Mb;
//    vprint CPS: "Mc norms:", Mc;

    beta := Max(Ma);
    alpha := Min(Ma cat Mb cat Mc);

//    vprint CPS: "Got alpha:", alpha;
//    vprint CPS: "Got beta:", beta;

    return [alpha, beta];

end function;

function NewCPSComplex(E, i)
/*
intrinsic CPSComplex(E::CrvEll, i::RngIntElt) -> FldReElt
{Complex Archimedean contribution to CPS lower and upper height bounds at a complex place}
K:=BaseField(E);
require Type(K) eq FldNum: "Base field must be a number field";
*/

    K:=BaseField(E);

//    vprint CPS: "CPSComplex E:", E;
//    vprint CPS: "K:", K;
//    vprint CPS: "i:", i;

    // embed in C using i'th embedding of K, i between r+1 and r+s:
    r,s:=Signature(K);
    assert r+1 le i and 1 le r+s; // "Invalid embedding number (must be Complex)"; 
    // Convert to Magma's numbering where complex conjugate embeddings are consecutive

    function make_polys(bI)
    b2,b4,b6,b8:=Explode(bI);
    f:=Polynomial([b6,2*b4,b2,4]);
    g:=Polynomial([-b8,-2*b6,-b4,0,1]);
    F:=Polynomial(Reverse([b6,2*b4,b2,4,0]));
    G:=Polynomial(Reverse([-b8,-2*b6,-b4,0,1]));
    return f, g, F, G;
    end function;

    bI := bInvariants(E);
    l, bIQ := CanChangeUniverse(bI, RationalField());
    if USE_EXACT and l then
    f, g, F, G := make_polys(bIQ);

//  vprint CPS: "Do exact ab";
//  vprint CPS: "f:", f;
//  vprint CPS: "g:", g;
    IndentPush();
//  vtime CPS:
ab:=alphabeta_exact(f, g);
    IndentPop();
//  vprint CPS: "Got ab:", ab;

//  vprint CPS: "Do exact AB";
//  vprint CPS: "F:", F;
//  vprint CPS: "G:", G;
    IndentPush();
//  vtime CPS:
AB:=alphabeta_exact(F, G);
    IndentPop();
//  vprint CPS: "Got AB:", AB;
    else

    if i gt r then i:=2*i-r-1; end if;

    /*
    b2,b4,b6,b8:=Explode([Conjugate(b,i) : b in bI]);

    f:=Polynomial([b6,2*b4,b2,4]);
    g:=Polynomial([-b8,-2*b6,-b4,0,1]);
    F:=Polynomial(Reverse([b6,2*b4,b2,4,0]));
    G:=Polynomial(Reverse([-b8,-2*b6,-b4,0,1]));
    */

    p := needed_alphabeta_prec(E, i);
    bI := [Conjugate(b,i: Precision:=p) : b in bI];
    f, g, F, G := make_polys(bI);

    BF<i> := BaseRing(F);
    //BF;
    _<z> := PolynomialRing(BF);
//  vprint CPS: "Do ab";
    Q := RationalField();
    //"rf:", Polynomial([Q!Round(x): x in Eltseq(f)]);
    //"rg:", Polynomial([Q!Round(x): x in Eltseq(g)]);
//  vtime CPS:
    ab:=alphabeta(f,g);
//  vprint CPS: "Got ab:", ab;
//  vprint CPS: "Do AB";
    //"F:", F; "G:", G;
    //"rF:", Polynomial([Q!Round(x): x in Eltseq(F)]);
    //"rG:", Polynomial([Q!Round(x): x in Eltseq(G)]);
//  vtime CPS:
    AB:=alphabeta(F,G);
//  vprint CPS: "Got AB:", AB;
    end if;

//    vprint CPS: "CPSComplex(",i,") returns ", [1/Max(ab[2],AB[2]), 1/Min(ab[1],AB[1])];
    return [1/Max(ab[2],AB[2]), 1/Min(ab[1],AB[1])];
end function;

function CPSComplex(E, i)
/*
intrinsic CPSComplex(E::CrvEll, i::RngIntElt) -> FldReElt
{Complex Archimedean contribution to CPS lower and upper height bounds at a complex place}
K:=BaseField(E);
require Type(K) eq FldNum: "Base field must be a number field";
*/

K:=BaseField(E);

    if 1 eq 1 then
    return NewCPSComplex(E, i);
    end if;

// embed in C using i'th embedding of K, i between r+1 and r+s:
r,s:=Signature(K);
assert r+1 le i and 1 le r+s; // "Invalid embedding number (must be Complex)"; 
// Convert to Magma's numbering where complex conjugate embeddings are consecutive
 if i gt r then i:=2*i-r-1; end if;
 p := needed_alphabeta_prec(E, i);
 b2,b4,b6,b8:=Explode([Conjugate(b,i : Precision:=p) : b in bInvariants(E)]);
 f:=Polynomial([b6,2*b4,b2,4]);
 g:=Polynomial([-b8,-2*b6,-b4,0,1]);
 F:=Polynomial(Reverse([b6,2*b4,b2,4,0]));
 G:=Polynomial(Reverse([-b8,-2*b6,-b4,0,1]));
 ab:=alphabeta(f,g);
 AB:=alphabeta(F,G);
 // "CPSComplex(",i,") returns ", [1/Max(ab[2],AB[2]), 1/Min(ab[1],AB[1])];
 return [1/Max(ab[2],AB[2]), 1/Min(ab[1],AB[1])];
end function;

//------------------------------------------------------
// This is the end of unmodified copied functions.


//Final function
//This function will give an upper bound for all quadratic fields


function CPSUpperBoundQuadraticFields(E)
// Archimedean part corresponds to:
// we change the field of the curve to an imaginary field, so that we can compute the imaginary contribution
    K1:=QuadraticField(-1);
    E1:=BaseChange(E,K1);
// We take the Maximum over the Archimedean contributions   
    B:=Max(2*Log(CPSComplex(E1, 1)[2]), 2*Log(CPSReal(E,1)[2]))/6;
// non-Archimedean part corresponds to:
    D:=Integers()!Discriminant(E);
// If the discriminant is even, we take into account the valuations above 2
    if D mod 2 eq 0 then
        // Here we add the part corresponding to 2
        B:=B+CPSEvenPrime(E,2);
        exp:=Factorisation(D)[1][2];
// we make sure that 2 does not divide D anymore.
        D:=Round(D*2^(-exp));
    end if;
    // This part corresponds to odd primes
    for p in PrimeDivisors(D) do
        B:=B+CPSOddPrimes(E,p);
        end for;
    return B;
end function;




//////////////////////////////// Code for point search /////////////////////////


/*This function takes an elliptic curve and a positive integer, 
  and finds the list of non-torsion points on quadratic fields Q(sqrt(D)) with
  D at most the given bound with height less than 10 */
function LowHeightPoints(E,B,Be);
  R<x> := PolynomialRing(Rationals());  
  //List of heights
  hlist:=[];
  // List of point, height
  list:=<>;
  // List of discriminants
  dlist:=[];

  // Set our search range to B if B is less than 10^5, otherwise, 10^3 - the majority of curves
  // for which we can provably find the point of smallest height have the point of smallest height defined over a field of discriminant
  // at most 10^3.
  if B le 10^5 then C := B; else C := 10^3; end if;

  for d in Exclude([-C..C],0) do
    if IsFundamentalDiscriminant(d) then
      // Construct quadratic field of discriminant <d>
      K<s> := NumberField(x^2 - d);
      // Extend base of E
      E_K := ChangeRing(E,K);
      // Find all points of *logarithmic* height at most 5 + bound. This way, if there is a point with canonical height less than 5, we will have 
      // found it. 
      pts := Points(E_K : Bound := Ceiling(5 + Be));
      for pt in pts do
        h := Height(pt);
        // For each of these points, store the height of the point, the current discriminant, and the pair of point and height. This format will be useful later.
        if Order(pt) eq 0 then hlist:= Append(hlist, h); list := Append(list,<pt, h>); dlist:=Append(dlist, d); end if; 
      end for;  
    end if; end for;
  return <list, hlist, dlist>;


end function;

/*The function takes an elliptic curve, and prints a line of data contianing
  the Cremona reference for the curve, the discriminant of the quadratic field
  where a point of minimal height occurs, a point of minimal height, and the height
  of that point.*/
function MinHeightE(E);
    Be:=CPSUpperBoundQuadraticFields(E);
    // Initial search for a point of small height
    R<x> := PolynomialRing(Rationals());
    provable := 1;
    ptlist := <>;
    disclist := [];
    hlist := [];
    for d in Exclude([-50..50],0) do
    if IsFundamentalDiscriminant(d) then
      // Construct quadratic field of discriminant <d>
      K<s> := NumberField(x^2 - d);
      // Extend base of E
      E_K := ChangeRing(E,K);
      // Find all points of *logarithmic* height at most 5 + Siksek bound. This way, if there is a point with canonical height less than 5, we will have 
      // found it.
      pts := Points(E_K : Bound := Ceiling(5 + Be));
      for pt in pts do
        h := Height(pt);
        // For each of these points, store the height of the point, the current discriminant, and the pair of point and height. This format will be useful later.
        if Order(pt) eq 0 then hlist:= Append(hlist, h); disclist:=Append(disclist, d); ptlist := Append(ptlist, pt); end if; 
      end for;  
    end if; end for;
    //Canonical height bound - see the accompanying paper
    if IsEmpty(hlist) eq false then;
      minValueInit, minIndexInit := Min(hlist);
      B:=Ceiling(Exp(2*minValueInit+2*Log(2)+4*Be));
    // If there are no points of small height in our initial search, then our result is not provably the smallest
    // NOTE: Because of a misunderstanding in the meaning of Magma's Bound parameter, this indicator is incorrect. It is still used for the initial search though
      //     so we leave it in, but removed it from the output datasets (and re-running this will not output the Provable indicator)
      //     To see which curves are provable, consult the "Provable_Curves" folder and data inside that folder.
    else B:=Ceiling(Exp(2*1+2*Log(2)+4*Be)); provable := 0;
    end if;
    LH:=LowHeightPoints(E, B, Be);
    // Create a flag for whether our point of smallest height is *provably* the point of smallest height over all quadratic fields.
    if B le 10^5 then provable := 1; else provable := 0; end if;
    if #LH[1] gt 0 then 
      minValue, minIndex := Min(LH[2]);
      P := LH[1][minIndex][1];
      minDisc := LH[3][minIndex];
      // If we found a smaller point in our initial search, then use that point instead
      if IsEmpty(hlist) eq false then;
        minValueInit, minIndexInit := Min(hlist);
        minPtInit := ptlist[minIndexInit];
        minDiscInit := disclist[minIndexInit];
        if minValue gt minValueInit then P := minPtInit; minDisc := minDiscInit; minValue := minValueInit; end if; 
      end if;
      //If the point is defined over Q, then put discriminant as 1  
      if IsCoercible(Rationals(), P[1]) and IsCoercible(Rationals(), P[2]) then print(CremonaReference(E) cat "," cat Sprint(1) cat "," cat Sprint(P) cat "," cat Sprint(minValue) cat "," cat Sprint(provable)); 
      //Otherwise, print the discriminant of the quadratic field over which the point is defined
      else print(CremonaReference(E) cat "," cat Sprint(minDisc) cat "," cat Sprint(P) cat "," cat Sprint(minValue) cat "," cat Sprint(provable)); end if;
    //Otherwise, there is no point of heigh less than 5 on the quadratic fields we searched
    //We call this E1 to distinguish from E2 - Siksek bound is too large.
    else print(CremonaReference(E) cat ",NA,NA,E1,NA");
    end if;
  return "";
end function;


/*This function creates the data on points of minimal height for all curves
  with a given range of conductors. Note that the output is stored as .txt files,
  one file for each conductor.*/
function GetHeightData(lbound, ubound);
  //Connect to Cremona Database
  db := CremonaDatabase();
  //For each conductor between <lbound> and <ubound>, find minimum height points for curves of that conductor
  for cond in [lbound..ubound] do
    curves := EllipticCurves(db, cond);
    if #curves gt 0 then
      //If there are curves with this conductor, make a file to store the output
      SetOutputFile("MinHeightData_" cat Sprint(cond) cat ".txt");
      //Add headers for data
      print("CremonaReference,Discriminant,Point,Height");
      //Create data for each elliptic curve
      for E in curves do
        MinHeightE(E);
      end for;
      //Save file
      UnsetOutputFile();
    end if;
  end for;
return "";
end function;