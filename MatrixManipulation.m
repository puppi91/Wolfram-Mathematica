(* ::Package:: *)

(*:Mathematica Version: 5.0  *)

(* :Copyright: Copyright 1989-2007, Wolfram Research, Inc.*)

(*:Context: LinearAlgebra`MatrixManipulation`  *)

(*:Title: Basic Matrix Manipulation Functions  *)

(*:Authors:   Kevin McIsaac, Daniel Lichtblau *)

(*:Summary:
This package provides basic matrix manipulation routines for composing a matrix
from block elements and extracting subblocks from a matrix.  Included are
functions for generating special matrices such as Hilbert and Hankel.
Also provided is a routine for extracting a matrix and right-hand-side
vector from a system of linear equations is a given set of variables, and
a routine to find the polar decomposition of a square matrix.

Finally, we have routines to find the norm of a vector, a matrix, or its
inverse. The vector p-norm, for a given vector vec and 1<=p<=Infinity, is
defined to be

Sum[Abs[v[[j]]]^p, {j,Length[p]}]^(1/p)

We implement this for a vector of approximate numbers. For a matrix mat, the
p-norm is defined to be the maximum, over all vectors vec of p-norm one, of
the p-norm of mat.vec. While it is in general not obvious how to compute
this, the cases where p is 1 or Infinity are trivial, and the case where p
is 2 is not hard. For the norms of the inverse matrix one can explicitly
compute Inverse[mat] and work from that, but it is asymptotically about
three times faster to work with the LUDecomposition/GETRF of mat. Hence we
allow either mat or its LUDecomposition/GETRF as an argument to
InverseMatrixNorm, with the latter case being significantly faster than the
former, which is in turn faster than MatrixNorm[Inverse[mat]] *)


(*:Limitations:

The matrix norm is only approximated for the case p=2. The inverse norm is
only approximated for all of the allowable values of p. Hence, while we
use the precision of the input the process of computing the norms, we only
return a machine number, as at best a few digits are correct. This is adequqate
because typically one is interested only in the order of magnitude of the norm.

The techniques used, while quite reasonable, may fail for specialized classes
of input. It should also be noted that any technique used to find the inverse
matrix norm (especially including explicit computation of the inverse matrix)
will fail if the input has inadequate precision. It is easy to recognize this
case, because the log of the condition number will typically be larger than
the precision of the input. In terms of efficiency and correctness, it is
clear from the code that one can get a good value for either the 1-or-infinity
norm of a matrix. If one is concerned that the matrix may be pathological for
the inverse-norm estimators, perhaps the safest ploy is to estimate the 2-norm
of the inverse; this uses the power method, and is fairly accurate. But note
that the 1-and-infinity estimators also use an abbreviated power-method
estimate as a reality check on the main method, so these should not do
anything drastically wrong. Note also that we use a fixed number of iterations
in the power-method computations. One could attain more accuracy (at expense
of run-time) by altering these to use e.g. FixedPoint with a SameTest option
to determine when the desired accuracy has been met.
*)

(*:Sources:   
G. Golub and C. Van Loan, Matrix Computations, The Johns Hopkins
University Press, 1996.

W. Hager. Condition Estimates. SIAM
J. Sci. Stat. Comput. 5(2). 311-316. June 1984

N. Higham. FORTRAN codes for estimating the one-norm of a real or complex
matrix , with applications to condition estimation. ACM Transactions on
Mathematical Software 14(4). 381-396. December 1988.  
*)

(*:Keywords: matrix, block, submatrix, linear equations,
polar decomposition, matrix norm, matrix condition number *)

(*:Requirements: None.  *)

(*:Package Version: 1.2 *)

(*:History:   Created January 25, 1989 by K. McIsaac.
        Updated February 4, 1989 by John Novak.
	LinearEquationsToMatrices added April 1995 by Daniel Lichtblau:
	    effectively replaced by kernel LinearEpression to matrix
	    rendering CheckLinearity option inappropriate rknapp 1/2000
	PolarDecomposition added October 1995 by Daniel Lichtblau
	HankelMatrix correction contributed by Jan Jelinek; minor
	  changes to error checking in LinearEquationsToMatrices and
	  PolarDecomposition, ECM,  Feb. 1997.
	Added VectorNorm, MatrixNorm, MatrixConditionNumber April 1997,
	  Daniel Lichtblau.
   	V1.2: Added LUMatrices, WRI 1998.

        Jan. 2001, Zbigniew Leyk: replaced matinvnorm1inf with
        `LAPACK`GECON; removed VectorNorm, vecnorminf, vecnorm1,
        vecnorminfPosition; replaced matnorminf and matnorm1 with LANGE;
        changed InverseMatrixNorm for p = 1 and Infinity; modified
        MatrixNorm

        Dec. 2002, Zbigniew Leyk: removed LUDecomposition and
        LUBackSubstitution and replaced them with GETRF and GETRS,
        respectively.

        April 2003, obsolete VectorNorm and MatrixNorm.

        Dec. 2003, Zbigniew Leyk: added new versions of InverseMatrixNorm
        and approxMatrixNorm which can work with sparse matrices. Note that
        approxMatrixNorm is now not equivalent to Norm. 
        Added EstimatedMatrix2Norm called by approxMatrixNorm.

        June 2005, Zbigniew Leyk: changed implementation of 
        PolarDecomposition. The implementation is now based on 
        SingularValueDecomposition.


*)

Message[General::obspkg, "LinearAlgebra`MatrixManipulation`"]
Quiet[
BeginPackage["LinearAlgebra`MatrixManipulation`",
             "Utilities`FilterOptions`"]
, {General::obspkg, General::newpkg}]


InsertRow::usage = "InsertRow[mat, r, p] inserts the row r into matrix mat so that r is pth row in the result."

InsertColumn::usage = "InsertColumn[mat, c, p] inserts the column c into the matrix mat so that c is the pth column in the result."

AppendColumns::usage=
"AppendColumns[mat1, mat2, ...] gives a new matrix composed of the \
submatrices mat1, mat2, ... , by joining their columns. The submatrices must \
all have the same number of columns."

AppendRows::usage=
"AppendRows[mat1, mat2, ...] gives a new matrix composed of the submatrices \
mat1, mat2, ..., by joining their rows. The submatrices must all have the same \
number of rows."

SquareMatrixQ::usage=
"SquareMatrixQ[mat] tests whether mat is a square matrix." 

TakeRows::usage=
"TakeRows[mat, part] takes the rows of matrix mat given by the partspec, \
part. This uses the same notation as Take."

TakeColumns::usage=
"TakeColumns[mat, part] takes the columns of matrix mat given by the \
partspec, part. This uses the same notation as Take."

TakeMatrix::usage=
"TakeMatrix[mat, start, end] gives the submatrix starting at position start \
and ending at position end, where each position is expressed as a  \
{row, column} pair, e.g., {1, 2}."

SubMatrix::usage=
"SubMatrix[mat, start, dim] gives the submatrix of dimension dim starting \
at position start in mat."

BlockMatrix::usage=
"BlockMatrix[block] is an obsolete function. Use ArrayFlatten[block] \
instead."

UpperDiagonalMatrix::usage=
"UpperDiagonalMatrix[f, m] gives an upper-diagonal matrix, m x m, \
using a function of two arguments f.  The (i,j)-th element of the matrix is \
f[i, j] for i >= j and zero otherwise."

LowerDiagonalMatrix::usage=
"LowerDiagonalMatrix[f, m] gives a lower-diagonal matrix, m x m, \
using a function of two arguments f.  The (i,j)-th element of the matrix is \
f[i, j] for i <= j and zero otherwise."

TridiagonalMatrix::usage=
"TridiagonalMatrix[f, m] gives a tridiagonal matrix, m x m, \
using a function of two arguments f.  The (i,j)-th element of the matrix is \
f[i,j] for Abs[i - j] <= 1 and zero otherwise."

ZeroMatrix::usage=
"ZeroMatrix[m] gives an m x m block matrix of zeros. ZeroMatrix[m, n] \
gives an m x n block matrix of zeros."

(*
HilbertMatrix::usage =
"HilbertMatrix[m,n] gives the m x n Hilbert Matrix, where the \
(i,j)-th element is defined as 1/(i + j - 1). HilbertMatrix[m] gives the  \
m x m Hilbert matrix."  
*)

(*
HankelMatrix::usage =
"HankelMatrix[column, row] gives the Hankel matrix defined by the \
given column and row; note that the last element of column must match the \
first element of row. HankelMatrix[col] gives the Hankel matrix whose first \
column is col, and where every element under the anti-diagonal is filled with \
zeros. HankelMatrix[n] gives the n x n Hankel matrix where the leading column \
is the integers 1, 2, ..., n."
*)

LinearEquationsToMatrices::usage =
"LinearEquationsToMatrices[eqns, vars] gives a list of the form {mat, vec}. \
The first element is the matrix of coefficients, the second is the vector of \
right-hand-sides, such that Thread[mat . vars == vec] gives eqns, possibly \
in expanded form."

PolarDecomposition::usage = 
"PolarDecomposition[mat] gives a list {u, s} comprising the polar \
decomposition of the matrix mat such that u . s == mat. Also, s is a \
positive semidefinite matrix. The matrix u satisfies the condition \
Transpose[Conjugate[u]] . u == IdentityMatrix[ Length[u[[1]] ]] if the \
number of rows of mat is greater then or equal to the number of columns; \
otherwise it satisfies the condition u . Transpose[Conjugate[u]] == \
IdentityMatrix[Length[u]]."

VectorNorm::usage =
"VectorNorm[vec] is obsolete. Use Norm instead.";

MatrixNorm::usage = 
"MatrixNorm[mat] is obsolete. Use Norm instead.";

InverseMatrixNorm::usage = 
"InverseMatrixNorm[mat] gives an estimate of the \
infinity-norm of the matrix Inverse[mat], where mat is a matrix of \
approximate numbers. Given an LUDecomposition lu for mat, \
InverseMatrixNorm[lu] gives an estimater of the infinity-norm of \
Inverse[mat]. InverseMatrixNorm[mat, p] and InverseMatrixNorm[lu, p] \
compute estimates of the p-norms, where p must be 1, 2, or Infinity."

MatrixConditionNumber::usage = 
"MatrixConditionNumber[mat] gives an estimate \
of the infinity-norm condition number of the matrix mat of approximate \
numbers. MatrixConditionNumber[mat, p] gives an estimate of the condition \
number in the p-norm, where p must be 1, 2, or Infinity."

LUMatrices::usage =
"LUMatrices[lu] gives a list {lmat, umat} containing the lower and upper \
triangular matrices produced by the LU decomposition of a matrix m, where \
lu is the combined matrix given by the first element of LUDecomposition[m]."

MatrixPlot::usage =
"MatrixPlot[mat] graphically displays the matrix with non-default values \
darkened. For arrays that are not sparse, the default value is 0. \
MatrixPlot[mat, val] displays with values not equal to val darkened.";

MatrixPlotScaling::usage =
"MatrixPlotScaling[min, max, (count)] generates tick marks suitable \
for use with MatrixPlot.";

MaxMatrixSize::usage =
"MaxMatrixSize is an option to MatrixPlot. It indicates the maximum \
number of elements on a side of the matrix display, compressing \
any matrix that is larger than the specified size. If Infinity, \
no compression occurs, and the output plot has the same number of \
elements as the matrix.";

LeftSide::usage = 
"Option for PolarDecomposition. If {z, p} = PolarDecomposition[mat, \
LeftSide->True] then mat = p.z. If {z, p} = PolarDecomposition[mat, \
LeftSide->False], then mat = z.p."

Begin["`Private`"]

issueObsoleteFunMessage[fun_, context_] :=
        (Message[fun::obspkgfn, fun, context];
         )

InsertRow[mat_?MatrixQ, r_, p_Integer] := 
(issueObsoleteFunMessage[InsertRow,"LinearAlgebra`MatrixManipulation`"];
	Insert[mat, If[MatchQ[mat, _SparseArray], SparseArray[r], r], p] /; 
    (1 <= p <= Length[mat] + 1 && 
        (VectorQ[r] && Length[r] == Dimensions[mat][[2]]) || 
        Not[ListQ[r]]))

InsertColumn[mat_?MatrixQ, c_?VectorQ, p_Integer] := 
(issueObsoleteFunMessage[InsertColumn,"LinearAlgebra`MatrixManipulation`"];
	Transpose[InsertRow[Transpose[mat], c, p]] /; 
    And[1 <= p <= Dimensions[mat][[2]] + 1,
        Length[c] == Length[mat]])

AppendColumns[l__?MatrixQ] := (issueObsoleteFunMessage[AppendColumns,"LinearAlgebra`MatrixManipulation`"];
	Join[l] /; SameColumnSize[{l}])

AppendRows[l__?MatrixQ] := (issueObsoleteFunMessage[AppendRows,"LinearAlgebra`MatrixManipulation`"];
	Transpose[Join @@ Transpose /@ {l}] /; 
            SameRowSize[{l}])

BlockMatrix[block_] :=
       (issueObsoleteFunMessage[BlockMatrix, "LinearAlgebra`MatrixManipulation`"];
	AppendColumns @@ Apply[AppendRows, block, {1}])

SquareMatrixQ[mat_?MatrixQ] := (issueObsoleteFunMessage[SquareMatrixQ,"LinearAlgebra`MatrixManipulation`"];
	SameQ @@ Dimensions[mat])

SameColumnSize[l_List] := (SameQ @@ (Dimensions[#][[2]]& /@ l) )

SameRowSize[l_List] := (SameQ @@ (Dimensions[#][[1]]& /@ l) )


TakeRows[mat_?MatrixQ, part_] := (issueObsoleteFunMessage[TakeRows,"LinearAlgebra`MatrixManipulation`"];
	Take[mat, part])

TakeColumns[mat_?MatrixQ, part_] := (issueObsoleteFunMessage[TakeColumns,"LinearAlgebra`MatrixManipulation`"];
	Take[mat, All, part])

TakeMatrix[mat_?MatrixQ, start:{startR_Integer, startC_Integer},
end:{endR_Integer, endC_Integer}] :=
	(issueObsoleteFunMessage[TakeMatrix,"LinearAlgebra`MatrixManipulation`"];
	Take[mat, {startR, endR}, {startC, endC}] /;
	And @@ Thread[Dimensions[mat] >= start] && 
	And @@ Thread[Dimensions[mat] >= end])

SubMatrix[mat_List, start:{_Integer, _Integer}, dim:{_Integer,_Integer}] :=
	(issueObsoleteFunMessage[SubMatrix,"LinearAlgebra`MatrixManipulation`"];
	TakeMatrix[mat, start, start+dim-1]) 

TridiagonalMatrix[fn_, size_Integer] :=
    (issueObsoleteFunMessage[TridiagonalMatrix,"LinearAlgebra`MatrixManipulation`"];
	Array[If[Abs[#1 - #2] <= 1, fn[##], 0]&, {size, size}] /;
        size >= 0)


LowerDiagonalMatrix[fn_, size_Integer] :=
	(issueObsoleteFunMessage[LowerDiagonalMatrix,"LinearAlgebra`MatrixManipulation`"];
	Array[If[#1>=#2, fn[#1, #2], 0]&, {size, size}] /;
	size >= 0)

UpperDiagonalMatrix[fn_, size_Integer] :=
	(issueObsoleteFunMessage[UpperDiagonalMatrix,"LinearAlgebra`MatrixManipulation`"];
	Array[If[#1<=#2, fn[#1, #2], 0]&, {size, size}] /;
	size >= 0)

ZeroMatrix[0, ___] := {}
ZeroMatrix[m_Integer, 0] := (issueObsoleteFunMessage[ZeroMatrix,"LinearAlgebra`MatrixManipulation`"];
	Table[{}, {m}])

ZeroMatrix[m_Integer,n_Integer] := 
	(issueObsoleteFunMessage[ZeroMatrix,"LinearAlgebra`MatrixManipulation`"];
	Normal[SparseArray[{},{m, n}]] /; m >= 0 && n>=0)

ZeroMatrix[m_Integer] := ZeroMatrix[m, m] /; m >= 0 

(*
HilbertMatrix[m_Integer,n_Integer] := 
	(issueObsoleteFunMessage[HilbertMatrix,"LinearAlgebra`MatrixManipulation`"];
	Table[1/(i+j-1), {i, m}, {j, n}])

HilbertMatrix[m_Integer] := HilbertMatrix[m,m]
*)

(*
HankelMatrix[size_Integer] :=
	HankelMatrix[Range[1,size]] /; size >= 0

HankelMatrix[col_List] :=
	(issueObsoleteFunMessage[HankelMatrix,"LinearAlgebra`MatrixManipulation`"];
	Module[{size = Length[col]},
		auxHankelMatrix[Join[col,Table[0,{size - 1}]],
			{size,size}]
	])

HankelMatrix[col_List,row_List] :=
	(issueObsoleteFunMessage[HankelMatrix,"LinearAlgebra`MatrixManipulation`"];
	(
	 auxHankelMatrix[Join[col,Drop[row,1]],
		{Length[col],Length[row]}]
	) /; Last[col] == First[row])

auxHankelMatrix[vec_List,size:{rows_Integer,cols_Integer}] :=
	(
	Array[(vec[[#1 + #2 - 1]])&,size]
	) /; Length[vec] >= (rows + cols - 1)
*)

LinearEquationsToMatrices[oeqns_, vars_List] := 
    (issueObsoleteFunMessage[LinearEquationsToMatrices,"LinearAlgebra`MatrixManipulation`"];
     Developer`LinearExpressionToMatrix[oeqns, vars])

Options[PolarDecomposition] = 
   {LinearAlgebra`MatrixManipulation`LeftSide -> True};

PolarDecomposition[mat_?MatrixQ, opts___?OptionQ] :=
  (issueObsoleteFunMessage[PolarDecomposition,"LinearAlgebra`MatrixManipulation`"];
	Module[{u, s, v, lside, m, n},
    {m, n} = Dimensions[mat]; 
    {u, s, v} = SingularValueDecomposition[mat, Min[m, n], Tolerance -> 0];
    lside = LinearAlgebra`MatrixManipulation`LeftSide /. 
                   Flatten[{opts}] /. Options[PolarDecomposition];
    If [lside,
      {u.ConjugateTranspose[v], v.s.ConjugateTranspose[v]}
      ,
      {u.ConjugateTranspose[v], u.s.ConjugateTranspose[u]}
    ]
  ])



LUPrecision[lu_] := Precision[lu[[1]]]

LUOkay[lu_] := Length[lu]==3 && lu[[3]]!=-1 && lu[[3]]=!=Infinity && 
  Precision[lu[[3]]]=!=Infinity 

LUSingularQ[lu_] := Length[lu]==3 && (lu[[3]]===Infinity || lu[[3]]==-1)

LUDim[lu_] := Length[lu[[2]]]


VectorNorm[vec_?VectorQ, p_:Infinity] := (issueObsoleteFunMessage[VectorNorm,"LinearAlgebra`MatrixManipulation`"];
	Norm[vec, p])

MatrixNorm[mat_?MatrixQ, p_:Infinity] /; (p==1 || p==2 || p===Infinity) := 
   (issueObsoleteFunMessage[MatrixNorm,"LinearAlgebra`MatrixManipulation`"];
	Norm[mat, p]);

approxMatrixNorm[mat_?MatrixQ, p_:Infinity] /; 
   (p==1 || p==2 || p===Infinity) := 
   (If [p == 2, EstimatedMatrix2Norm[mat], Norm[mat, p]])

EstimatedMatrix2Norm[mat_] := Module[ 
       {j, x, y, len = Length[mat], prec = Precision[mat]},
       x = Table[Random[Real, {10, 11}, prec], {len}];
       For [j = 1, j <= 5, j++,
            x /= Norm[x, Infinity];
            y = x;
            x = mat.x;
            x = Conjugate[Transpose[mat]].x;
            x = SetPrecision[x, prec];
       ];
       Sqrt[Norm[x]/Norm[y]]
]

matinvnorm2[lu_] := Module[
	{len=LUDim[lu], prec=LUPrecision[lu]+10, x, y},
	x = Table[Random[Real, {10, 11}, prec], {len}];
	For [j=1, j<=5, j++,
		y = x;
                LinearAlgebra`LAPACK`GETRS["N", Evaluate[lu[[1]]], 
                                  Evaluate[lu[[2]]], x];
                LinearAlgebra`LAPACK`GETRS["C", Evaluate[lu[[1]]], 
                                  Evaluate[lu[[2]]], x];
		x = SetPrecision[x, prec]
	];
	Re[N[(x.Conjugate[x] / y.Conjugate[y])^(1/4)]]
]



InverseMatrixNorm[lu_List, p_:Infinity] /; (p==1 || p==2 || p===Infinity) :=
  (issueObsoleteFunMessage[InverseMatrixNorm,"LinearAlgebra`MatrixManipulation`"];
	Module[{rcond, prec = LUPrecision[lu], lu1 = lu},
        (* lu should be generated by LUDecomposition *)
 	If [p==1, 
            LinearAlgebra`LAPACK`GECON["1",Evaluate[lu1[[1]]], 1, rcond];
            If [rcond > 0, 1/rcond, Infinity]
          ,
            If [p===Infinity, 
                LinearAlgebra`LAPACK`GECON["Infinity",Evaluate[lu1[[1]]], 
                                            1, rcond];
                If [rcond > 0, 1/rcond, Infinity]
              , 
                matinvnorm2[lu1]
            ]
	]
  ] /; LUOkay[lu])

InverseMatrixNorm[lu_, p_:Infinity] :=
	(issueObsoleteFunMessage[InverseMatrixNorm,"LinearAlgebra`MatrixManipulation`"];
	Infinity /; ((p==1 || p==2 || p===Infinity) && LUSingularQ[lu]));

(* used only for testing *)
EstimatedMatrix1Norm[mat_] := Module[ 
   {x, est = 1, kase = 0},
   x = Table[1, {Length[mat]}];
   While [ True,
           Check [
               Internal`DeactivateMessages[
                   LinearAlgebra`LAPACK`LACON[x, est, kase]]
               ,
               Return[Indeterminate]
               ,
               LinearAlgebra`LAPACK`LACON::blnotsym
           ];
           If [kase == 0, Break[]];
           If [kase == 1,
               x = mat.x;
             , (* kase == 2 *)
               x = Transpose[mat].x;
           ]
   ];
   est
]


InverseMatrixNorm1I[mat_, p_] :=
  Module[{matFact, x, est = 1, kase = 0},
     Check[  (* check singularity *)
            matFact = Internal`DeactivateMessages[LinearSolve[mat]];
           ,
            Return[Infinity]
           ,
            LinearSolve::sing1
     ];
     x = Table[1, {Length[mat]}];
     If [ p == 1,
          While [ True,
             Check [
                 Internal`DeactivateMessages[
                      LinearAlgebra`LAPACK`LACON[x, est, kase]]
                 ,
                 Return[Indeterminate]
                 ,
                 LinearAlgebra`LAPACK`LACON::blnotsym
             ];
             If [kase == 0, Break[]];
             If [kase == 1,
                 x = matFact[x];
               , (* kase == 2 *)
                 x = matFact[x, "C"];
             ]
          ];
       , (* p === Infinity *)
          While [ True,
             Check [
                 Internal`DeactivateMessages[
                     LinearAlgebra`LAPACK`LACON[x, est, kase]]
                 ,
                 Return[Indeterminate]
                 ,
                 LinearAlgebra`LAPACK`LACON::blnotsym
             ];
             If [kase == 0, Break[]];
             If [kase == 1,
                 x = matFact[x, "C"];
               , (* kase == 2 *)
                 x = matFact[x];
             ]
          ];
     ];
     est
  ]


InverseMatrixNorm[mat_?SquareMatrixQ, p_:Infinity] /; 
   (p==1 || p===Infinity) := 
(issueObsoleteFunMessage[InverseMatrixNorm,"LinearAlgebra`MatrixManipulation`"];
	Module[{norm, prec = Precision[mat], bad},
        bad = EstimatedMatrix1Norm[mat]; 
        InverseMatrixNorm1I[mat, p] /; 
                (If [bad === Indeterminate,
                      Message[InverseMatrixNorm::symb]; False, True]
                  && If [prec===Infinity,
		         Message[InverseMatrixNorm::prec];  False, True])
])

matinvnorm2[matFact_, len_, prec_] := Module[
       {j, x, y},
       x = Table[Random[Real, {10, 11}, prec], {len}];
       For [j = 1, j <= 5, j++,
            x /= Norm[x, Infinity];
            y = x;
            x = SetPrecision[ matFact[ matFact[x], "C"], prec];
       ];
       Sqrt[Norm[x]/Norm[y]]
]

InverseMatrixNorm[mat_?SquareMatrixQ, p_:Infinity] /; (p==2) :=
  (issueObsoleteFunMessage[InverseMatrixNorm,"LinearAlgebra`MatrixManipulation`"];
	Module[{bad, prec = Precision[mat], matFact},
        bad =  EstimatedMatrix1Norm[mat];
        (
          Check[  (* check singularity *)
             matFact = Internal`DeactivateMessages[LinearSolve[mat]];
            ,
             Return[Infinity]
            ,
             LinearSolve::sing1
          ];
          matinvnorm2[matFact, Length[mat], prec]
        ) /;
         (If [bad===Indeterminate,
                   Message[InverseMatrixNorm::symb]; False, True]
          && If [prec===Infinity,
		Message[InverseMatrixNorm::prec];  False, True])
  ])


MatrixConditionNumber::pnorm =
"The second argument of MatrixConditionNumber should be 1, 2 or Infinity."

MatrixConditionNumber::prec = 
"MatrixConditionNumber has received a matrix with infinite precision."

InverseMatrixNorm::prec =
"InverseMatrixNorm has received a matrix with infinite precision."

MatrixConditionNumber::symb =
"MatrixConditionNumber has received a matrix with non-numerical values."

InverseMatrixNorm::symb =
"InverseMatrixNorm has received a matrix with non-numerical values."

MatrixConditionNumber[mat_?SquareMatrixQ, lu_, p_:Infinity] /; LUOkay[lu] :=
	(issueObsoleteFunMessage[MatrixConditionNumber,"LinearAlgebra`MatrixManipulation`"];
	Module[{prec = Precision[mat]},
         (
	  approxMatrixNorm[mat,p] * InverseMatrixNorm[lu,p]
	 ) /; ( If [prec===Infinity,
		Message[MatrixConditionNumber::prec]; False, True]
              &&
              If [p != 1 && p != 2 && p =!= Infinity,
                  Message[MatrixConditionNumber::pnorm]; False, True] )
	])

MatrixConditionNumber[mat_?SquareMatrixQ, p_:Infinity] :=
	(issueObsoleteFunMessage[MatrixConditionNumber,"LinearAlgebra`MatrixManipulation`"];
	Module[{prec = Precision[mat], bad},
        bad = EstimatedMatrix1Norm[mat];
        (
         If [p == 1 || p === Infinity,
             (* use internal function *)
             LinearAlgebra`MatrixConditionNumber[mat, Norm->p]
           , (* p == 2 *) 
	    approxMatrixNorm[mat,p] * InverseMatrixNorm[mat,p] ]
        ) /; (If [bad===Indeterminate,
                   Message[MatrixConditionNumber::symb]; False, True]
             && If [prec===Infinity,
                Message[MatrixConditionNumber::prec]; False, True]
             && If [p != 1 && p != 2 && p =!= Infinity,
                  Message[MatrixConditionNumber::pnorm]; False, True]   
                )
	])

LUMatrices[lud_List] := LUMatrices[lud[[1]]]/; LUOkay[lud]

LUMatrices[lu_?MatrixQ]:=
  (issueObsoleteFunMessage[LUMatrices,"LinearAlgebra`MatrixManipulation`"];
	Module[{l, u, k = Length[lu], prec = Precision[lu]},
        u = lu Table[If[i<=j, 1, 0], {i,k}, {j,k}];
        l = lu - u + IdentityMatrix[k];
        {l, u}
  ])

(* Matrix Plot *)

Unprotect[MatrixPlot];

StringName[sym_Symbol] := SymbolName[sym];
StringName[name_] := name;
stripOptions[opt2___, discard_List] := 
  Module[{opt = Flatten[{opt2}]},
   (*get rid of the options in the discard list*)
   Map[(opt = stripOptions[opt, #]) &, discard];
   opt];
stripOptions[opt2___, OP_] := 
  Module[{opt = opt2, pos},
   (*get rid of the option OP*)
   Delete[opt, Position[opt, (g_?(StringName[#] === StringName[OP] &) -> _)]]
   ];
defaultOpt = {MaxMatrixSize -> 512, FrameTicks->All};
defaultOptnames = Flatten[Map[{#[[1]], StringName[#[[1]]]}&, defaultOpt]];
combinedopt = Join[
      defaultOpt,
      stripOptions[Options[ArrayPlot], defaultOptnames]
     ];
ord = Ordering[Map[#[[1]]&, combinedopt]];

Options[MatrixPlot] = combinedopt[[ord]];

(*
Options[MatrixPlot] = {MaxMatrixSize -> 512} ~Join~ stripOptions[Options[ArrayPlot], FrameTicks];
*)

MatrixPlot[A_?MatrixQ, opts___?OptionQ]:= (issueObsoleteFunMessage[MatrixPlot,"LinearAlgebra`MatrixManipulation`"];
	With[
   {res = MatrixPlotInternal[A, 0, opts]},  
   res/;(res =!= $Failed)
]);
MatrixPlot[A_?MatrixQ, center_, opts___?OptionQ]:= (issueObsoleteFunMessage[MatrixPlot,"LinearAlgebra`MatrixManipulation`"];
	With[
   {res = MatrixPlotInternal[A,center, opts]},  
   res/;(res =!= $Failed)
]);
MatrixPlotInternal[A_?MatrixQ, center_, opts___?OptionQ]:= Module[
   {maxsize, res,i,j,ccf,cf},
   {maxsize} = {MaxMatrixSize}/.Flatten[{opts, Options[MatrixPlot]}];
   If[maxsize =!= Infinity &&
      (!IntegerQ[maxsize] || maxsize <= 1), maxsize = 512];
   {cf,ft} = {ColorFunction,FrameTicks}/.
        Options[{opts, Options[MatrixPlot]}]/.{ColorFunction->Automatic, FrameTicks->All};
   If [cf===Automatic, 
      ccf[x_]:= If[x =!= center, Black, White],
      ccf = cf;
   ];
   res = ArrayPlot[A,MaxPlotPoints->maxsize, ColorFunction->ccf,
       FrameTicks->ft,
       FilterOptions[ArrayPlot, opts],
       FilterOptions[Graphics, opts]
   ];
   If [Head[res] === ArrayPlot, $Failed, res]
];

Protect[MatrixPlot];

End[]

EndPackage[]
