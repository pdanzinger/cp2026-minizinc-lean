#pragma once

// Forward declarations for all MzTerm classes
// This file is used to break circular dependencies

class MzTerm;

// Literals
class MzIntLit;
class MzBoolLit;
class MzSetLit;
class MzIntSetRange;

// Operators
class MzBinOpCmp;
class MzBinOpArith;
class MzBinOpBool;
class MzBinOpSet;
class MzUnOpInt;
class MzUnOpBool;

// Functions
class MzBinFunc;
class MzUnFunc;
class MzFuncCall;
class MzLibraryFunction;

// Arrays
class MzArrayAccess;
class MzArrayComprehension;
class MzArrayLit;
class MzArrayView;

// Aggregators
class MzAggregator;
class MzComprehensionAggregator;

// Misc
class MzVarDecl;
class MzId;
class MzSetMembership;
class MzSubset;
class MzQuantifier;
class MzSetComprehension;
class MzITE;
class MzLetIn;
class MzCumulative;
class MzCircuit;
class MzAllDifferent;

// Other declarations
class MzFuncDecl;
