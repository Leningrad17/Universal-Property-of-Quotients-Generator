
//Arbitrarily defined sets
sig A, B, C {}


//Produces set maps where all elements of the domain are mapped
pred IsTotal[X,Y:set univ, f: X -> Y] {
	all x : X | some x.f }

//Checks that the composition of two total set maps is total
assert CompOfTotalisTotal{
	all f: A -> B | all g : B -> C | (IsTotal[A,B,f] and IsTotal[B,C,g]) implies IsTotal[A,C,f.g]
}

check CompOfTotalisTotal for 4 A, 4 B, 4 C


//Produces set maps where every element of the domain is mapped to at most one element of the codomain
pred IsWellDefined[X,Y:set univ, f:X -> Y] {
	all x : X | lone x.f}

//Checks that the composition of two well defined set maps is well defined
assert CompOfWellDefinedisWellDefined{
	all f: A -> B | all g : B -> C | (IsWellDefined[A,B,f] and IsWellDefined[B,C,g]) implies IsWellDefined[A,C,f.g]
}

check CompOfWellDefinedisWellDefined for 4 A, 4 B, 4 C

//Produces set maps which are functions
pred IsFunction[X,Y: set univ, f: X -> Y] {
	IsTotal[X,Y,f] and IsWellDefined[X,Y,f]
}

//Checks that the composition of two functions is a function
assert CompOfFunctionisFunction {
	all f : A -> B | all g : B -> C | (IsFunction[A,B,f] and IsFunction[B,C,g]) implies IsFunction[A,C,f.g]
}

check CompOfFunctionisFunction for 4 A, 4 B, 4 C

//Produces functions where every element of the codomain is mapped to from at most one element of the domain
pred IsInjective[X,Y : set univ, f: X -> Y] {
	IsFunction[X,Y,f] and all y: Y | lone f.y }

//Checks that the composition of injective functions is injective
assert CompOfInjectiveisInjective {
	all f : A -> B | all g : B -> C | (IsInjective[A,B,f] and IsInjective[B,C,g]) implies IsInjective[A,C,f.g]
}

check CompOfInjectiveisInjective for 4 A, 4 B, 4 C

//Produces functions where every element of the codomain is mapped to from at least one element of the domain
pred IsSurjective[X,Y:set univ, f: X -> Y] {
	IsFunction[X,Y,f] and all y : Y | some f.y
}

//Checks that the composition of surjective functions is surjective
assert CompOfSurjectiveisSurjective {
	all f: A -> B | all g : B -> C | (IsSurjective[A,B,f] and IsSurjective[B,C,g]) implies IsSurjective[A,C,f.g]
}

check CompOfSurjectiveisSurjective for 4 A, 4 B, 4 C

//Produces functions which are both injective and surjective
pred IsBijective[X,Y : set univ, f : X -> Y] {
	IsInjective[X,Y,f] and IsSurjective[X,Y,f]
}

//Checks that the composition of bijective functions is bijective
assert CompOfBijectiveisBijective {
	all f: A -> B | all g : B -> C | (IsBijective[A,B,f] and IsBijective[B,C,g]) implies IsBijective[A,C,f.g]
}

check CompOfBijectiveisBijective for 4 A, 4 B, 4 C





