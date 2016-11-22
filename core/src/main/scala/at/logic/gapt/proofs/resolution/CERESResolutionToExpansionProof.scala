package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs.expansion.{ ETMerge, ExpansionProofWithCut, ExpansionSequent, ExpansionTree, eliminateMerges }
import at.logic.gapt.proofs.Sequent
import scala.collection.mutable

/**
 * Converts a resolution proof of some CERES Characteristic Clause Set into an ExpansionProof.
 *
 * Partial ExpansionSequents of projections corresponding to clauses in CharacteristicClauseSet are given (as input),
 * partial means: we extract ExpansionSequents from projections and remove clause parts.
 *
 * Then these partial ExpansionSequents are substituted (in Subst step) and merged (in Resolution step).
 */
object CERESResolutionToExpansionProof {

  val mergeChildren = mutable.Set[ExpansionTree]()

  def apply( proof: ResolutionProof, input: Input => ExpansionSequent ): ExpansionProofWithCut = {
    val memo = mutable.Map[ResolutionProof, ExpansionSequent]()

    def f( p: ResolutionProof ): ExpansionSequent = memo.getOrElseUpdate( p, p match {
      case in: Input => input( in )

      case Resolution( q1, i1, q2, i2 ) =>
        var expansionSequent: ExpansionSequent = Sequent()
        for ( t1 <- f( q1 ).antecedent ) {
          for ( t2 <- f( q2 ).antecedent ) {
            if ( t1.shallow == t2.shallow ) {
              mergeChildren.clear()
              mergeChildren.add( t1 )
              mergeChildren.add( t2 )
              expansionSequent +:= ETMerge( t1.shallow, Polarity.InAntecedent, mergeChildren )
            }
          }
        }
        for ( t1 <- f( q1 ).succedent ) {
          for ( t2 <- f( q2 ).succedent ) {
            if ( t1.shallow == t2.shallow ) {
              mergeChildren.clear()
              mergeChildren.add( t1 )
              mergeChildren.add( t2 )
              expansionSequent :+= ETMerge( t1.shallow, Polarity.InSuccedent, mergeChildren )
            }
          }
        }
        expansionSequent

      case Subst( q, subst ) =>
        subst( f( q ) )
    } )

    eliminateMerges( ExpansionProofWithCut( f( proof ) ) )
  }
}
