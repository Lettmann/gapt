package at.logic.gapt.examples.tip.isaplanner

import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

/* This proof is not a s.i.p. */
object isaplanner23 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( file"examples/tip/isaplanner/prop_23.smt2" )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    induction( hov"a:Nat" )
    allR
    allL( "h1", le"b:Nat" )
    eql( "h1_0", "goal" ).fromLeftToRight
    induction( hov"b:Nat" )
    allL( "h1", le"Z:Nat" )
    eql( "h1_1", "goal" ).fromLeftToRight
    refl
    allL( "h2", le"b_0:Nat" )
    eql( "h2_0", "goal" ).fromLeftToRight
    refl
    allR
    induction( hov"b:Nat" )
    allL( "h1", le"S(a_0:Nat):Nat" )
    allL( "h2", le"a_0:Nat" )
    eql( "h2_0", "goal" ).fromLeftToRight
    eql( "h1_0", "goal" ).fromLeftToRight
    refl
    allL( "h3", le"a_0:Nat", le"b_0:Nat" )
    allL( "h3", le"b_0:Nat", le"a_0:Nat" )
    allL( "IHa_0", le"b_0:Nat" )
    eql( "h3_0", "goal" )
    eql( "h3_1", "goal" )
    eql( "IHa_0_0", "goal" ).fromLeftToRight
    refl

  }
}
