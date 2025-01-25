open util/integer
//Arbitrarily defined sets
sig A, Q, C {}


//Produces set maps where all elements of the domain are mapped
pred IsTotal[X,Y:set univ, f: X -> Y] {
	all x : X | some x.f }

//Checks that the composition of two total set maps is total
assert CompOfTotalisTotal{
	all f: A -> Q | all g : Q -> C | (IsTotal[A,Q,f] and IsTotal[Q,C,g]) implies IsTotal[A,C,f.g]
}

check CompOfTotalisTotal for 4 A, 4 Q, 4 C


//Produces set maps where every element of the domain is mapped to at most one element of the codomain
pred IsWellDefined[X,Y:set univ, f:X -> Y] {
	all x : X | lone x.f}

//Checks that the composition of two well defined set maps is well defined
assert CompOfWellDefinedisWellDefined{
	all f: A -> Q | all g : Q -> C | (IsWellDefined[A,Q,f] and IsWellDefined[Q,C,g]) implies IsWellDefined[A,C,f.g]
}

check CompOfWellDefinedisWellDefined for 4 A, 4 Q, 4 C

//Produces set maps which are functions
pred IsFunction[X,Y: set univ, f: X -> Y] {
	IsTotal[X,Y,f] and IsWellDefined[X,Y,f]
}

//Checks that the composition of two functions is a function
assert CompOfFunctionisFunction {
	all f : A -> Q | all g : Q -> C | (IsFunction[A,Q,f] and IsFunction[Q,C,g]) implies IsFunction[A,C,f.g]
}

check CompOfFunctionisFunction for 4 A, 4 Q, 4 C

//Produces functions where every element of the codomain is mapped to from at most one element of the domain
pred IsInjective[X,Y : set univ, f: X -> Y] {
	IsFunction[X,Y,f] and all y: Y | lone f.y }

//Checks that the composition of injective functions is injective
assert CompOfInjectiveisInjective {
	all f : A -> Q | all g : Q -> C | (IsInjective[A,Q,f] and IsInjective[Q,C,g]) implies IsInjective[A,C,f.g]
}

check CompOfInjectiveisInjective for 4 A, 4 Q, 4 C

//Produces functions where every element of the codomain is mapped to from at least one element of the domain
pred IsSurjective[X,Y:set univ, f: X -> Y] {
	IsFunction[X,Y,f] and all y : Y | some f.y
}

//Checks that the composition of surjective functions is surjective
assert CompOfSurjectiveisSurjective {
	all f: A -> Q | all g : Q -> C | (IsSurjective[A,Q,f] and IsSurjective[Q,C,g]) implies IsSurjective[A,C,f.g]
}

check CompOfSurjectiveisSurjective for 4 A, 4 Q, 4 C

//Produces functions which are both injective and surjective
pred IsBijective[X,Y : set univ, f : X -> Y] {
	IsInjective[X,Y,f] and IsSurjective[X,Y,f]
}

//Checks that the composition of bijective functions is bijective
assert CompOfBijectiveisBijective {
	all f: A -> Q | all g : Q -> C | (IsBijective[A,Q,f] and IsBijective[Q,C,g]) implies IsBijective[A,C,f.g]
}

check CompOfBijectiveisBijective for 4 A, 4 Q, 4 C

//Produces relations on a set which are reflexive
pred IsReflexive[X: set univ, f: X -> X] {
	all x : X | (x -> x) in f 
}

//Produces relations on a set which are symmetric
pred IsSymmetric[X : set univ, f: X -> X] {
	all x : X | all y : X | (x-> y) in f implies (y -> x) in f 
}


//Produces relations on a set which are transitive
pred IsTransitive [X: set univ, f: X -> X] {
	all x : X | all y : X | all z : X | (x -> y) in f and (y -> z) in f implies (x -> z) in f
}

//Produces equivalence relations on a set
pred IsEquivalence[X: set univ, f : X -> X]{
	IsReflexive[X,f] and IsSymmetric[X,f] and IsTransitive[X,f]
}

//Defines a mapping between the distinct equivalence classes of a set such that each equivalence class maps to 
//another equivalence class exactly once; the purpose of this is to calculate the number of distinct equivalence 
//classes, where the cardinality of g is exactly that number. 
pred EquivClassMap[X : set univ, f : X -> X, g : X -> X] {
	(all x : X | one x2 : x.*f | one x3 : X - x.*f | x2.g = x3 and #(x.*f <: g) = 1) or ((some x : X | #X = #x.*f) implies one x : X | g = x -> x)
}

//Maps elements from different equivalence classes to each other. Used to calculate the number of
//equivalence classes for a given equivalence relation
pred IsNotEquivalence[X,Y: set univ, f: X -> X, g : X -> X] {
	IsEquivalence[X,f] and EquivClassMap[X,f,g]
}

//Calculates the size of the equivalence class with representative x 
fun EquivalenceClassSize[X : set univ, f: X -> X, x : X] : Int {
	#(x.*f) }

//Calculates the number of different equivalence classes of an equivalence relation
fun EquivalenceClassPartitions[X: set univ, f: X -> X, g : X-> X] : Int {
	#g }

//Produces functions which are invariant to the equivalence defined on the domain
pred IsInvariant[X,Y : set univ, f : X -> X, g : X -> Y] {
	IsEquivalence[X,f] and IsFunction[X,Y,g] and all x1, x2 : X | (x1 -> x2) in f implies (x1.g = x2.g)
}

//Produces surjective function which maps each element of the set endowed with an equivalence
//relation to its respective equivalence class in the quotient set
pred IsQuotientMap [X, Y : set univ, f : X -> X, g : X -> Y, h : X -> X] {
	IsNotEquivalence[X,Y,f,h] and IsFunction[X,Y,g] and IsSurjective[X,Y,g] and all x1, x2 : X | (x1 -> x2) in f iff (x1.g = x2.g)
}


//Produces as many elements of the quotient set as there are equivalence classes for a sharper image
pred QuotientSetEqualsEquivalenceClasses [X,Y:set univ, f : X -> X, g : X -> X] {
	(IsNotEquivalence[X,Y,f,g] and some x : X | lt[EquivalenceClassSize[X,f,x],#X]) implies #Y = EquivalenceClassPartitions[X,f,g] else #Y = 1
}

//Produces the quotient map without excess elements of the quotient set
pred TrueQuotientMapRepresentation [X,Y : set univ, f : X -> X, g : X -> Y, h : X -> X] {
	IsQuotientMap[X,Y,f,g,h] and QuotientSetEqualsEquivalenceClasses[X,Y,f,h]
}

//Produces the commutative diagram representing the universal property of the quotient set
pred UniversalPropertyGenerator {
	some f, i: A -> A | some g : A -> Q |  some h : A -> C | some j : Q -> C | IsInvariant[A,C,f,h] and TrueQuotientMapRepresentation[A,Q,f,g, i] and all a : A | a.h = a.g.j     
}

	
run UniversalPropertyGenerator for 3 A, 3 Q, 3 C, 10 Int




	





