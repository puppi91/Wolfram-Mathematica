#!/usr/bin/env wolframscript
(* ::Package:: *)

ClearAll[t1,t2,t3,t4,h,eps]
t1 = 0.625;
t2 = t1+h;
t3 = t2+h;
t4 = t3+h;
(*t2 = 0.75;
t3 = 0.875;
t4 = 1;*)
(*f = Sin[x-(t2+eps)];*)
f = -Log[x/(t2+eps)];
B1= ((t3-x)^2)/(2*h^2);
B2 = ((x-t1)*(t3-x))/(2*h^2)+((t4-x)*(x-t2))/(2*h^2);
B3= ((x-t2)^2)/(2*h^2);
M11 = Integrate[B1*B1,{x,t2,t3}];
M12 = Integrate[B1*B2,{x,t2,t3}];
M13 = Integrate[B1*B3,{x,t2,t3}];
M21 = Integrate[B2*B1,{x,t2,t3}];
M22 = Integrate[B2*B2,{x,t2,t3}];
M23 = Integrate[B2*B3,{x,t2,t3}];
M31 = Integrate[B3*B1,{x,t2,t3}];
M32 = Integrate[B3*B2,{x,t2,t3}];
M33 = Integrate[B3*B3,{x,t2,t3}];
F1 = Integrate[f*B1,{x,t2,t3}];
F2 = Integrate[f*B2,{x,t2,t3}];
F3 =  Integrate[f*B3,{x,t2,t3}];
M = {{M11,M12,M13},{M21,M22,M23},{M31,M32,M33}};
F={{F1},{F2},{F3}};
lambda = LinearSolve[M,F];


Print[lambda[[1]]];


M11bis = Integrate[B1*B1,{x,t2,t2+eps}];
M12bis = Integrate[B1*B2,{x,t2,t2+eps}];
M13bis = Integrate[B1*B3,{x,t2,t2+eps}];
M21bis =Integrate[ B2*B1,{x,t2,t2+eps}];
M22bis =Integrate[B2*B2,{x,t2,t2+eps}];
M23bis = Integrate[B2*B3,{x,t2,t2+eps}];
M31bis = Integrate[B3*B1,{x,t2,t2+eps}];
M32bis = Integrate[B3*B2,{x,t2,t2+eps}];
M33bis = Integrate[B3*B3,{x,t2,t2+eps}];
Mbis = {{M11bis ,M12bis ,M13bis},{M21bis ,M22bis ,M23bis},{M31bis ,M32bis ,M33bis}};
lambdabis = LinearSolve[Mbis,F];


Print[lambdabis[[1]]]


F1bis = Integrate[f*B1,{x,t2,t2+eps}];
F2bis = Integrate[f*B2,{x,t2,t2+eps}];
F3bis =  Integrate[f*B3,{x,t2,t2+eps}];
Fbis={{F1bis},{F2bis},{F3bis}};
lambdatris = LinearSolve[Mbis,Fbis];


Print[lambdatris[[1]]]
