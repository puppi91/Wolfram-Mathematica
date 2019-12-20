#!/usr/bin/env wolframscript
(* ::Package:: *)

Clear[a]
phi1 = 1-x-y+x*y;
phi2 = x-x*y;
phi3 = x*y;
phi4 = y-x*y;

Gradphi1 = {-1+y, -1+x};
Gradphi2 = {1-y, -x};
Gradphi3 = {y, x};
Gradphi4 = {-y, 1-x};


n = 2;
epsilon = ConstantArray[0, n];
condnumb = ConstantArray[0, n];
j = 1;
For[i=1,i<n+1, i++,
a = 10.^(-i);

phi1phi2 = Integrate[phi1*phi2,{x,0,a},{y,0,-x+a}];
phi1phi3 = Integrate[phi1*phi3,{x,0,a},{y,0,-x+a}];
phi1phi4 = Integrate[phi1*phi4,{x,0,a},{y,0,-x+a}];
phi2phi3 = Integrate[phi2*phi3,{x,0,a},{y,0,-x+a}];
phi2phi4 = Integrate[phi2*phi4,{x,0,a},{y,0,-x+a}];
phi3phi4 = Integrate[phi3*phi4,{x,0,a},{y,0,-x+a}];

Dphi1Dphi2 = Integrate[Gradphi1.Gradphi2,{x,0,a},{y,0,-x+a}];
Dphi1Dphi3 = Integrate[Gradphi1.Gradphi3,{x,0,a},{y,0,-x+a}];
Dphi1Dphi4 = Integrate[Gradphi1.Gradphi4,{x,0,a},{y,0,-x+a}];
Dphi2Dphi3 = Integrate[Gradphi2.Gradphi3,{x,0,a},{y,0,-x+a}];
Dphi2Dphi4 = Integrate[Gradphi2.Gradphi4,{x,0,a},{y,0,-x+a}];
Dphi3Dphi4 = Integrate[Gradphi3.Gradphi4,{x,0,a},{y,0,-x+a}];

normphi1 = Sqrt[Integrate[phi1*phi1,{x,0,a},{y,0,-x+a}]+Integrate[Gradphi1.Gradphi1,{x,0,a},{y,0,-x+a}]];
normphi2 = Sqrt[Integrate[phi2*phi2,{x,0,a},{y,0,-x+a}]+Integrate[Gradphi2.Gradphi2,{x,0,a},{y,0,-x+a}]];
normphi3 = Sqrt[Integrate[phi3*phi3,{x,0,a},{y,0,-x+a}]+Integrate[Gradphi3.Gradphi3,{x,0,a},{y,0,-x+a}]];
normphi4 = Sqrt[Integrate[phi4*phi4,{x,0,a},{y,0,-x+a}]+Integrate[Gradphi4.Gradphi4,{x,0,a},{y,0,-x+a}]];


A12 = (phi1phi2 + Dphi1Dphi2)/(normphi1*normphi2);
A13 = (phi1phi3 + Dphi1Dphi3)/(normphi1*normphi3);
A14 = (phi1phi4 + Dphi1Dphi4)/(normphi1*normphi4);
A23 = (phi2phi3 + Dphi2Dphi3)/(normphi2*normphi3);
A24 = (phi2phi4 + Dphi2Dphi4)/(normphi2*normphi4);
A34 = (phi3phi4 + Dphi3Dphi4)/(normphi3*normphi4);
A = {{1, A12, A13, A14}, {A12, 1, A23, A24}, {A13, A23, 1, A34}, {A14, A24, A34, 1}};
MatrixForm[A];
lambdas=Eigenvalues[A];
condnumb[[j]] = lambdas[[1]]/lambdas[[4]];
epsilon[[j]] = a;
Print[lambdas[[1]]/lambdas[[4]]];
Print [a];
j = j + 1;
]
Print [epsilon]
Print[condnumb]
















