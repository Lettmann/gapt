package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.prover9.Prover9

/**
 * Repeatedly applies unary rules that are unambiguous
 */
case object DecomposeTactic extends Tactical {
  def apply( proofState: ProofState ) = {
    RepeatTactic(
      NegLeftTactic() orElse
        NegRightTactic() orElse
        AndLeftTactic() orElse
        OrRightTactic() orElse
        ImpRightTactic() orElse
        ForallRightTactic() orElse
        ExistsLeftTactic()
    )( proofState )
  }
}

case class DestructTactic( applyToLabel: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    def canDestruct( formula: HOLFormula, index: SequentIndex ): Boolean = ( formula, index ) match {
      case ( All( _, _ ), Suc( _ ) ) => true
      case ( Ex( _, _ ), Ant( _ ) )  => true
      case ( And( _, _ ), _ )        => true
      case ( Or( x, y ), _ )         => true
      case ( Imp( x, y ), _ )        => true
      case ( Neg( _ ), _ )           => true
      case _                         => false
    }

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, formula ), index ) <- goalSequent.zipWithIndex.elements if canDestruct( formula, index ) )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, _ ), index ) <- goalSequent.zipWithIndex.elements )
          yield index
    }

    // Select some formula index!
    indices.headOption match {
      case Some( i ) =>
        val ( existingLabel, _ ) = goalSequent( i )

        val tac = allR( existingLabel ) orElse
          exL( existingLabel ) orElse
          andL( existingLabel ) orElse
          andR( existingLabel ) orElse
          orL( existingLabel ) orElse
          orR( existingLabel ) orElse
          impL( existingLabel ) orElse
          impR( existingLabel ) orElse
          negL( existingLabel ) orElse
          negR( existingLabel )
        tac( goal )
      case None => None
    }
  }
}

/**
 * Chain
 */
case class ChainTactic( hyp: String, target: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val hypIndex = ( for ( ( ( `hyp`, All( _, _ ) ), index ) <- goalSequent.zipWithIndex.elements ) yield index ).headOption

    // Proceed only if a (universally quantified) hypothesis exists
    hypIndex match {
      case None => None
      case Some( i ) if i.isInstanceOf[Ant] =>
        // Extract hypothesis
        val ( _, quantifiedFormula ) = goalSequent( i )
        val All( hypVar, hypInner ) = quantifiedFormula

        // Extract formula to match against target
        def f( x: HOLFormula ): HOLFormula = x match {
          case Imp( _, r ) => f( r )
          case _           => x
        }

        val hypTargetMatch = f( hypInner )

        // Find target index and substitution
        val t = {
          target match {
            case Some( x ) =>
              ( for (
                ( ( `x`, y ), index ) <- goalSequent.zipWithIndex.succedent;
                sub <- syntacticMatching( hypTargetMatch, y )
              ) yield ( x, index, sub ) ).headOption
            case None =>
              ( for (
                ( ( x, y ), index ) <- goalSequent.zipWithIndex.succedent;
                sub <- syntacticMatching( hypTargetMatch, y )
              ) yield ( x, index, sub ) ).headOption
          }
        }

        // Proceed only if a matching formula exists
        t match {
          case None => None
          case Some( ( targetLabel, targetIndex, sub ) ) =>

            // Recursively apply implication left to the left until the end of the chain is reached,
            // where the sequent is an axiom (following some contractions).
            // The right premises of the implication left rules become new sub goals,
            // but where the initial target formula is then "forgotten".
            def g( x: Sequent[( String, HOLFormula )], y: SequentIndex ): LKProof = x( y ) match {
              case ( existingLabel, And( lhs, rhs ) ) =>
                AndRightRule(
                  g( x.delete( y ) :+ ( existingLabel, lhs ), Suc( x.succedent.length - 1 ) ),
                  g( x.delete( y ) :+ ( existingLabel, rhs ), Suc( x.succedent.length - 1 ) ),
                  And( lhs, rhs )
                )
              case _ =>
                OpenAssumption( x )
            }

            def f( x: Sequent[( String, HOLFormula )], y: SequentIndex, outermostCall: Boolean = false ): LKProof = {
              x( y ) match {
                case ( existingLabel, Imp( lhs, rhs ) ) =>
                  // Different methods must be applied depending on how the chain is defined.
                  val premiseLeft = lhs match {
                    case And( _, _ ) if outermostCall =>
                      WeakeningLeftRule( g( x.delete( targetIndex ).delete( y ) :+ ( existingLabel -> lhs ), Suc( x.succedent.length - 1 ) ), rhs )
                    case _ =>
                      forget( targetLabel )( OpenAssumption( x.delete( y ) :+ ( existingLabel -> lhs ) ) ).get
                  }

                  val premiseRight = f( ( existingLabel -> rhs ) +: x.delete( y ), Ant( 0 ) )

                  ImpLeftRule( premiseLeft, premiseRight, Imp( lhs, rhs ) )

                case _ =>
                  axiomLog( OpenAssumption( x ) ).get
              }
            }

            val auxFormula = sub( hypInner )
            val newGoal = goalSequent.insertAt( i + 1, NewLabel( goalSequent, hyp ) -> auxFormula )
            val premise = f( newGoal, i + 1, true )
            val auxProofSegment = ForallLeftRule( premise, quantifiedFormula, sub.map.get( hypVar ).get )
            Option( ContractionLeftRule( auxProofSegment, quantifiedFormula ) )

        }

      case Some( i ) if i.isInstanceOf[Suc] =>
        None
    }
  }

  def at( target: String ) = new ChainTactic( hyp, Option( target ) )
}

/**
 * Paramodulation tactic
 */
case class ParamodulationTactic( mainFormulaLabel: String, axiom: HOLAtom, targetFormula: HOLFormula ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = for ( ( ( `mainFormulaLabel`, _ ), index ) <- goalSequent.zipWithIndex.elements )
      yield index

    indices.headOption match {
      case Some( sequentIndex ) =>

        axiom match {
          case Eq( _, _ ) =>

            val cutLabel = NewLabel( goalSequent, mainFormulaLabel + "_cut" )

            val leftPremise = TheoryAxiom( Sequent( Nil, Seq( axiom ) ) )
            val rightPremiseTmp = OpenAssumption( ( cutLabel, axiom ) +: goalSequent )

            val ( cutIndex, rightPremise ) = sequentIndex match {
              case Ant( _ ) =>
                ( Ant( 1 ), eqL( cutLabel, mainFormulaLabel ).to( targetFormula )( rightPremiseTmp ) )
              case Suc( _ ) =>
                ( Ant( 0 ), eqR( cutLabel, mainFormulaLabel ).to( targetFormula )( rightPremiseTmp ) )
            }

            for ( p <- rightPremise )
              yield CutRule( leftPremise, Suc( 0 ), p, cutIndex )

          case _ => None
        }

      case None => None
    }
  }

}

/**
 * Solves propositional sub goal
 */
case object PropTactic extends Tactic {
  override def apply( goal: OpenAssumption ) = {
    solve.solvePropositional( goal.conclusion )
  }
}

/**
 * Solves sub goal with Prover9
 */
case object Prover9Tactic extends Tactic {
  override def apply( goal: OpenAssumption ) = {
    Prover9.getLKProof( goal.conclusion )
  }
}

case object EscargotTactic extends Tactic {
  override def apply( goal: OpenAssumption ) = Escargot getLKProof goal.conclusion
}
