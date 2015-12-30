package at.logic.gapt.proofs.gaptic

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lk._

/**
 * Immutable object defining the current state of the proof in the tactics language.
 * @param currentGoalIndex
 * @param proofSegment
 */
case class ProofState( currentGoalIndex: Int, proofSegment: LKProof ) {
  val initSegment = proofSegment.endSequent

  val subGoals: Seq[OpenAssumption] =
    for ( OpenAssumption( s ) <- proofSegment.treeLike.postOrder )
      yield OpenAssumption( s )

  require( currentGoalIndex >= 0 && currentGoalIndex <= subGoals.length )

  /**
   *
   * Constructor with name of theorem and initial formula.
   */
  def this( proofSegment: LKProof ) = this( 0, proofSegment )

  /**
   * Returns the sub goal at a given index if it exists.
   * @param i
   * @return
   */
  def getSubGoal( i: Int ): Option[OpenAssumption] = Option( subGoals( i ) )

  /**
   * Returns a string representation of a sub goal at a given index.
   * @param i
   * @return
   */
  def displaySubGoal( i: Int ): String = {
    getSubGoal( i ) match {
      case Some( o: OpenAssumption ) => o.s.toString
      case None                      => "No sub goal found with index " + i
    }
  }

  /**
   * Returns a new proof state if the new sub goal index is valid
   * @param i
   * @return
   */
  def setCurrentSubGoal( i: Int ): Option[ProofState] =
    if ( subGoals isDefinedAt i ) Some( copy( currentGoalIndex = i ) ) else None

  /**
   * Replaces the i-th open assumption by an arbitrary proof segment and returns the result in a new proof state.
   * @param openAssumption
   * @param replacementSegment
   * @return
   */
  def replaceSubGoal( openAssumption: Int, replacementSegment: LKProof ): ProofState = {
    var assumptionIndex = -1

    // Replacement function - applied recursively
    def f( p: LKProof ): LKProof = p match {
      // Open assumption. Replace on matching index.
      case OpenAssumption( _ ) =>
        assumptionIndex += 1
        if ( assumptionIndex == openAssumption )
          replacementSegment
        else
          p
      // Case distinction on rules
      case InitialSequent( s )                                         => Axiom( s )
      case ContractionLeftRule( subProof, index1, _ )                  => ContractionLeftRule( f( subProof ), subProof.conclusion( index1 ) )
      case ContractionRightRule( subProof, index1, _ )                 => ContractionRightRule( f( subProof ), subProof.conclusion( index1 ) )
      case WeakeningLeftRule( subProof, formula )                      => WeakeningLeftRule( f( subProof ), formula )
      case WeakeningRightRule( subProof, formula )                     => WeakeningRightRule( f( subProof ), formula )
      case CutRule( leftSubProof, index1, rightSubProof, index2 )      => CutRule( f( leftSubProof ), leftSubProof.conclusion( index1 ), f( rightSubProof ), rightSubProof.conclusion( index2 ) )
      case NegLeftRule( subProof, index )                              => NegLeftRule( f( subProof ), subProof.conclusion( index ) )
      case NegRightRule( subProof, index )                             => NegRightRule( f( subProof ), subProof.conclusion( index ) )
      case AndLeftRule( subProof, index1, index2 )                     => AndLeftRule( f( subProof ), subProof.conclusion( index1 ), subProof.conclusion( index2 ) )
      case AndRightRule( leftSubProof, index1, rightSubProof, index2 ) => AndRightRule( f( leftSubProof ), leftSubProof.conclusion( index1 ), f( rightSubProof ), rightSubProof.conclusion( index2 ) )
      case OrLeftRule( leftSubProof, index1, rightSubProof, index2 )   => OrLeftRule( f( leftSubProof ), leftSubProof.conclusion( index1 ), f( rightSubProof ), rightSubProof.conclusion( index2 ) )
      case OrRightRule( subProof, index1, index2 )                     => OrRightRule( f( subProof ), subProof.conclusion( index1 ), subProof.conclusion( index2 ) )
      case ImpLeftRule( leftSubProof, index1, rightSubProof, index2 )  => ImpLeftRule( f( leftSubProof ), leftSubProof.conclusion( index1 ), f( rightSubProof ), rightSubProof.conclusion( index2 ) )
      case ImpRightRule( subProof, index1, index2 )                    => ImpRightRule( f( subProof ), subProof.conclusion( index1 ), subProof.conclusion( index2 ) )
      case ForallLeftRule( subProof, _, a, term, v )                   => ForallLeftRule( f( subProof ), All( v, a ), term )
      case ForallRightRule( subProof, index, ev, qv )                  => ForallRightRule( f( subProof ), All( qv, Substitution( ev, qv )( subProof.conclusion( index ) ) ), ev )
      case ExistsLeftRule( subProof, index, ev, qv )                   => ExistsLeftRule( f( subProof ), Ex( qv, Substitution( ev, qv )( subProof.conclusion( index ) ) ), ev )
      case ExistsRightRule( subProof, _, a, term, v )                  => ExistsRightRule( f( subProof ), Ex( v, a ), term )
      case EqualityLeftRule( subProof, eq, index, pos )                => EqualityLeftRule( f( subProof ), subProof.conclusion( eq ), subProof.conclusion( index ), pos )
      case EqualityRightRule( subProof, eq, index, pos )               => EqualityRightRule( f( subProof ), subProof.conclusion( eq ), subProof.conclusion( index ), pos )
      case DefinitionLeftRule( subProof, index, main )                 => DefinitionLeftRule( f( subProof ), subProof.conclusion( index ), main )
      case DefinitionRightRule( subProof, index, main )                => DefinitionRightRule( f( subProof ), subProof.conclusion( index ), main )
      case _ =>
        throw new Exception( "Unmatched LK rule: " + p + ". Could not replace sub goal." )
    }

    val newSegment = f( proofSegment )

    ProofState( currentGoalIndex, newSegment )
  }
}

/**
 * Defines the case class open assumption which considers an arbitrary labelled sequence an axiom.
 * @param s
 */
case class OpenAssumption( s: Sequent[( String, HOLFormula )] ) extends InitialSequent {
  override def conclusion = s map { labelledFormula => labelledFormula._2 }
}

trait Tactical {
  /**
   *
   * @param proofState
   * @return
   */
  def apply( proofState: ProofState ): Option[ProofState]
}

trait Tactic extends Tactical {
  /**
   *
   * @param goal
   * @return
   */
  def apply( goal: OpenAssumption ): Option[LKProof]

  /**
   *
   * @param proofState
   * @return
   */
  override def apply( proofState: ProofState ): Option[ProofState] = {
    for {
      goal <- proofState getSubGoal proofState.currentGoalIndex
      proofSegment <- this( goal )
    } yield proofState.replaceSubGoal( proofState currentGoalIndex, proofSegment )
  }
}

/**
 * Object that wraps helper function to generate eigen variable that is fresh (in OpenAssumption sub goal).
 */
object FreshVariable {
  /**
   * Actual helper function for a fresh variable.
   * @param subGoal
   * @param quantifiedVariable
   * @return
   */
  def apply( subGoal: OpenAssumption, quantifiedVariable: Var ): Var = {
    val varName = quantifiedVariable.name
    val regex = f"$varName%s_([0-9]+)".r

    // Get integer subscripts (i.e 1, 2, 3 for x_1, x_2, x_3)
    val usedVariableSubscripts = {
      for ( Var( s, _ ) <- freeVariables( subGoal.conclusion ); m <- regex findFirstMatchIn s )
        yield Integer parseInt ( m group 1 )
    }.toList.sorted

    def f( s: Seq[Int] ): Int = s match {
      case h1 :: ( h2 :: t ) if ( h2 > h1 + 1 ) => h1 + 1
      case h1 :: ( h2 :: t )                    => f( h2 :: t )
      case h :: t if t.length == 0              => h + 1
    }

    val subscript =
      usedVariableSubscripts.headOption match {
        case None                   => 0
        case Some( min ) if min > 0 => 0
        case _                      => f( usedVariableSubscripts )
      }

    FOLVar( f"$quantifiedVariable%s_$subscript%d" )
  }

}