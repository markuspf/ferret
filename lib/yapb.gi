#############################################################################
##
##
#W  yapb.gi                Ferret Package                Chris Jefferson
##
##  Installation file for functions of the Ferret package.
##
#Y  Copyright (C) 2013-2014 University of St. Andrews, North Haugh,
#Y                          St. Andrews, Fife KY16 9SS, Scotland
##

####
# Functions and variables beginning '_YAPB' are only called
# from C++ by YAPB.
####

_YAPB_Globals := [];

_YAPB_addRef := function(obj)
  Add(_YAPB_Globals, obj);
end;

_YAPB_checkRef := function(obj)
  return ForAny(_YAPB_Globals, x -> IsIdenticalObj(x, obj));
end;

_YAPB_clearRefs := function()
  _YAPB_Globals := [];
end;

_YAPB_getPermTo := function(sc, i)
  local current_perm, current_pos, base_val;
  base_val := sc.orbit[1];
  if not(IsBound(sc.transversal[i])) then
    return fail;
  fi;
  current_perm := sc.transversal[i];
  current_pos := i^current_perm;
  while (current_pos <> base_val)
  do
    current_perm := current_perm * sc.transversal[current_pos];
    current_pos := i^current_perm;
  od;
  return current_perm;
end;

_YAPB_inGroup := function(p, g)
  return (p in g);
end;

_YAPB_isGroupConj := function(p, g)
  return g^p = g;
end;

_YAPB_getOrbitPart := function(g, i)
  return OrbitsDomain(Group(g.generators), [1..i]);
end;

_YAPB_getBlockList := function(sc)
  local blocks, g, orbs, b, o;
  g := Group(sc.generators);
  orbs := Orbits(g);
  blocks := [];
  for o in orbs
  do
    b := RepresentativesMinimalBlocks(g,o);
    if b[1] <> o then
      Append(blocks, b);
    fi;
  od;

  return List(blocks, x->Orbit(g,Set(x),OnSets));
end;

_YAPB_FixedOrbits := function(group, domainsize, fixedpoints)
    return OrbitsDomain(Stabilizer(group, fixedpoints, OnTuples), [1..domainsize]);
end;

_YAPB_RepresentElement := function(group, list1, list2)
    local res;
    res := RepresentativeAction(group, list1, list2, OnTuples);
    if(res = fail) then
        return fail;
    fi;
    return ListPerm(res);
end;

_YAPB_getInfoFerret := function()
  return InfoLevel(InfoFerret);
end;

_YAPB_getInfoFerretDebug := function()
  return InfoLevel(InfoFerretDebug);
end;

_YAPB_getOrbitalList := function(G, cutoff)
	local orb, orbitsG, iorb, graph, graphlist, val, p, i, orbsizes, orbpos, innerorblist, orbitsizes,
		  biggestOrbit, skippedOneLargeOrbit;
	
	graphlist := [];
	orbitsG := Orbits(G);
	
	orbsizes := [];
	orbpos := [];
	# Efficently store size of orbits of values
	for orb in [1..Length(orbitsG)] do
		for i in orbitsG[orb] do
			orbsizes[i] := Size(orbitsG[orb]);
			orbpos[i] := orb;
		od;
	od;
	
	innerorblist := List(orbitsG, o -> Orbits(Stabilizer(G, o[1]), [1..LargestMovedPoint(G)]));

    orbitsizes := List([1..Length(orbitsG)], 
	  x -> List(innerorblist[x], y -> Size(orbitsG[x])*Size(y)));
	
	biggestOrbit := Maximum(Flat(orbitsizes));

	skippedOneLargeOrbit := false;


	for i in [1..Size(orbitsG)] do
		orb := orbitsG[i];
		for iorb in innerorblist[i] do
			if (Size(orb) * Size(iorb) = biggestOrbit and not skippedOneLargeOrbit) then
				skippedOneLargeOrbit := true;
			else
				if (Size(orb) * Size(iorb) <= cutoff) and
				# orbit size unchanged
				not(Size(iorb) = orbsizes[iorb[1]]) and
				# orbit size only removed one point
				not(orbpos[orb[1]] = orbpos[iorb[1]] and Size(iorb) + 1 = orbsizes[iorb[1]])
					then
					graph := List([1..LargestMovedPoint(G)], x -> []);
					for val in orb do
						p := RepresentativeAction(G, orb[1], val); 
						graph[val] := List(iorb, x -> x^p);
					od;
					Add(graphlist, graph);
				fi;
			fi;
		od;
	od;
	return graphlist;
end;

#####
# END OF FUNCTIONS CALLED FROM C++ CODE
#####

#############################################################################
##
##
##  <#GAPDoc Label="ConStabilize">
##  <ManSection>
##  <Heading>ConStabilize</Heading>
##  <Func Name="ConStabilize" Arg="object, action" Label="for an object and an action"/>
##  <Func Name="ConStabilize" Arg="object, n" Label="for a transformation or partial perm"/>
##
##  <Description>
##  In the first form this represents the group which stabilises <A>object</A>
##  under <A>action</A>.
##  The currently allowed actions are OnSets, OnSetsSets, OnSetsDisjointSets,
##  OnTuples, OnPairs and OnDirectedGraph.
##
##  In the second form it represents the stabilizer of a partial perm
##  or transformation in the symmetric group on <A>n</A> points.
##
##  Both of these methods are for constructing arguments for the
##  <Ref Func="Solve" /> method.
##
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
InstallMethod(ConStabilize, [IsList, IsFunction],
function(list, op)
  if op = OnSets then
    return rec(constraint := "SetStab",
               arg := list,
               max := MaximumList(list, 0));
  fi;

  if op = OnSetsDisjointSets then
    return rec(constraint := "SetSetStab",
               arg := list,
               max := MaximumList(List(list, x -> MaximumList(x, 0)),0));
  fi;

  if op = OnSetsSets then
    return rec(constraint := "OverlappingSetSetStab",
               arg := list,
               max := MaximumList(List(list, x -> MaximumList(x, 0)),0));
  fi;

  if op = OnTuples or op = OnPairs then
    return rec(constraint := "ListStab",
               arg := list,
               max := MaximumList(list, 0));
  fi;

  if op = OnTuplesTuples then
      return rec(constraint := "ListStab",
                 arg := Concatenation(list),
                 max := MaximumList(Concatenation(list), 0));
  fi;

  if op = OnTuplesSets then
     return List(list, x -> ConStabilize(x, OnSets));
  fi;

  if op = OnDirectedGraph then
    return rec(constraint := "DirectedGraph",
               arg := list,
               max := Length(list));
  fi;
  
  if op = OnEdgeColouredDirectedGraph then
      return rec(constraint := "EdgeColouredDirectedGraph",
                 arg := list,
                 max := Length(list));
  fi;

  Error("Do not understand:", op);
end);

InstallMethod(ConStabilize, [IsList, IsFunction, IsRecord],
  function(list, op, useroptions)
    local con, options;
    
    if Size(RecNames(useroptions)) = 0 then
      return ConStabilize(list, op);
    fi;
  
    if op = OnEdgeColouredDirectedGraph then
      con := rec(constraint := "EdgeColouredDirectedGraph",
                 arg := list,
                 max := Length(list));
    elif op = OnDirectedGraph then
      con := rec(constraint := "DirectedGraph",
               arg := list,
               max := Length(list));
    else
      ErrorNoReturn("No record argument allowed for " + op);
    fi;
    
     useroptions := _FerretHelperFuncs.fillUserValues(
          rec(start_path_length := 1,
              normal_path_length := 1), useroptions);
     
     con.start_path_length := useroptions.start_path_length;
     con.normal_path_length := useroptions.normal_path_length;
     
     return con;
  end);
  
  

InstallMethod(ConStabilize, [IsPosInt, IsFunction],
function(i, op)
  if op = OnPoints then
    return rec(constraint := "SetStab",
               arg := [i],
               max := i);
  fi;

  Error("Do not understand:", op);
end);

InstallMethod(ConStabilize, [IsTransformation, IsPosInt],
function(t, i)
  return ConStabilize(List([1..i], x -> [x^t]), OnDirectedGraph);
end);

InstallMethod(ConStabilize, [IsPartialPerm, IsPosInt],
function(pp, m)
  local l, i;
  l := List([1..m], x -> []);
  for i in [1..m] do
    if i^pp <> 0 then
      Add(l[i], i^pp);
    fi;
  od;
  return ConStabilize(l, OnDirectedGraph);
end);

#############################################################################
##
##
##  <#GAPDoc Label="ConInGroup">
##  <ManSection>
##  <Func Name="ConInGroup" Arg="G"/>
##
##  <Description>
##  Represents the permutation group <A>G</A>, as an argument for
##  <Ref Func="Solve" />.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
InstallMethod(ConInGroup, [IsPermGroup],
function(G)
  return ConInGroup(G, rec() );
end);

# Inefficient, StabChain, BlockStabChain, OrbStabChain, BlockOrbStabChain, UnorderedStabChain

InstallMethod(ConInGroup, [IsPermGroup, IsRecord],
function(G, useroptions)

  useroptions := _FerretHelperFuncs.fillUserValues(
          rec(orbits := true, blocks := false, orbitals := false), useroptions);

  # We special case the identity group, because it is a pain
  if IsTrivial(G) then
    return rec(constraint:="FixAllPoints", max := 1);
  else
    return rec(constraint:= "Generators_StabChain",
               arg := G,
               orbits := useroptions.orbits,
               blocks := useroptions.blocks,
               orbitals := useroptions.orbitals,
               max := LargestMovedPoint(G));
  fi;
end);


InstallGlobalFunction( OnDirectedGraph, function(graph, perm)
  local newgraph, list, i, j;
  newgraph := [];
  for i in [1..Length(graph)] do
    list := [];
    for j in [1..Length(graph[i])] do
      Add(list, (graph[i][j])^perm);
    od;
    if i^perm > Length(graph) then
      ErrorNoReturn("perm invalid on graph");
    fi;
    newgraph[i^perm] := Set(list);
  od;
  return newgraph;
end );

InstallGlobalFunction( OnEdgeColouredDirectedGraph, function(graph, perm)
  local newgraph, list, i, j;
  newgraph := [];
  for i in [1..Length(graph)] do
    list := [];
    for j in [1..Length(graph[i])] do
      Add(list, [(graph[i][j][1])^perm, graph[i][j][2]]);
    od;
    if i^perm > Length(graph) then
      ErrorNoReturn("perm invalid on graph");
    fi;
    newgraph[i^perm] := Set(list);
  od;
  return newgraph;
end );

_FERRET_DEFAULT_OPTIONS := rec(searchValueHeuristic := "RBase",
                               searchFirstBranchValueHeuristic := "RBase",
                               rbaseCellHeuristic := "smallest",
                               rbaseValueHeuristic := "smallest",
                               stats := false,
                               recreturn := false,
                               only_find_generators := true,
                               just_rbase := false
                               );

#############################################################################
##
##
##  <#GAPDoc Label="Solve">
##  <ManSection>
##  <Func Name="Solve" Arg="constraints [,rec]"/>
##
##  <Description>
##  Finds the intersection of the list <A>constraints</A>.
##
##  Each member of <A>constraints</A> should be a group or coset
##  generated by one of <Ref Func="ConInGroup" /> or
##  ConStabilize.
##
##  The optional second argument allows configuration options to be
##  passed in.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
InstallGlobalFunction( Solve, function( arg )
  local maxpoint, record, l, options, useroptions,
        constraints, name, buildStabChain, retgrp;
  l := Length(arg);
  if l = 0 or l > 2 then
    Error( "usage: Solve(<C>[, <options>])");
  fi;

  constraints := Filtered(Flat(arg[1]), x -> x.max > 0);

  if Length(constraints) = 0 then
    Error("Cannot create infinite group in Solve");
  fi;

  maxpoint := Maximum(List(constraints, x -> x.max));

  # YAPB++ requires at least 2 points. We solve this in this way
  # because it makes sure we return all the various things
  # users might want (an rbase, etc).
  if maxpoint < 2 then
    Add(constraints, rec(constraint:="FixAllPoints", max := 2));
    maxpoint := 2;
  fi;

  if l = 2 then
    useroptions := arg[2];
  else
    useroptions := rec();
  fi;

  options := _FerretHelperFuncs.fillUserValues(_FERRET_DEFAULT_OPTIONS,
                                               useroptions);

  options.size := maxpoint;

  if options.stats or options.just_rbase then
    options.recreturn := true;
  fi;

  record := YAPB_SOLVE(constraints, options);
  _YAPB_clearRefs();

  # We now stitch together a stabilizer chain from the return values of YAPB++
  buildStabChain := function(gens, gen_map)
    local sc, current_val, start_of_range, i;
    current_val := gen_map[1][1];
    start_of_range := 1;
    sc := EmptyStabChain(gens, ());
    for i in [2..Length(gen_map)] do
      if gen_map[i][1] <> current_val then
        InsertTrivialStabilizer(sc, current_val);
        AddGeneratorsExtendSchreierTree(sc, gens{[start_of_range..i-1]});
        current_val := gen_map[i][1];
        start_of_range := i;
      fi;
    od;
    InsertTrivialStabilizer(sc, current_val);
    AddGeneratorsExtendSchreierTree(sc, gens{[start_of_range..Length(gens)]});
    return sc;
  end;

  if options.recreturn then
    return record;
  else
    if record.generators = [()] then # just to avoid having to make code work in this case
      retgrp := Group(());
      StabChainMutable(retgrp);
    else
      retgrp := Group(record.generators);
      SetStabChainMutable(retgrp, buildStabChain(record.generators, record.generators_map));
    fi;

    Size(retgrp);
    return retgrp;
  fi;

end );

InstallGlobalFunction( SolveCoset, function( arg )
  local maxpoint, record, l, options, useroptions,
        cCommon, cLeft, cRight, name, buildStabChain, retgrp;
  l := Length(arg);
  if l <> 3 and l <> 4 then
    Error( "usage: Solve(<C-Common>, <C-Left>, <C-Right> [, <options>])");
  fi;

  cCommon := Filtered(Flat(arg[1]), x -> x.max > 0);
  cLeft := Flat(arg[2]);
  cRight := Flat(arg[3]);

  if Length(cLeft) <> Length(cRight) then
    Error("Length(cLeft) must equal Length(cRight)");
  fi;

  if Length(cCommon) = 0 and Length(cLeft) = 0 then
    Error("Must have an least one constraint");
  fi;

  maxpoint := Maximum(List(Flat([cCommon, cLeft, cRight]), x -> x.max));

  if l = 2 then
    useroptions := arg[2];
  else
    useroptions := rec();
  fi;

  options := _FerretHelperFuncs.fillUserValues(_FERRET_DEFAULT_OPTIONS,
                                               useroptions);

  options.size := maxpoint;

  if options.stats or options.just_rbase then
    options.recreturn := true;
  fi;

  record := YAPB_SOLVE_COSET(cCommon, cLeft, cRight, options);
  _YAPB_clearRefs();

  # We now stitch together a stabilizer chain from the return values of YAPB++
  buildStabChain := function(gens, gen_map)
    local sc, current_val, start_of_range, i;
    current_val := gen_map[1][1];
    start_of_range := 1;
    sc := EmptyStabChain(gens, ());
    for i in [2..Length(gen_map)] do
      if gen_map[i][1] <> current_val then
        InsertTrivialStabilizer(sc, current_val);
        AddGeneratorsExtendSchreierTree(sc, gens{[start_of_range..i-1]});
        current_val := gen_map[i][1];
        start_of_range := i;
      fi;
    od;
    InsertTrivialStabilizer(sc, current_val);
    AddGeneratorsExtendSchreierTree(sc, gens{[start_of_range..Length(gens)]});
    return sc;
  end;

  if options.recreturn then
    return record;
  else
    if record.generators = [()] then # just to avoid having to make code work in this case
      retgrp := Group(());
      StabChainMutable(retgrp);
    else
      retgrp := Group(record.generators);
      SetStabChainMutable(retgrp, buildStabChain(record.generators, record.generators_map));
    fi;

    Size(retgrp);
    return retgrp;
  fi;

end );
#E  files.gi  . . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
