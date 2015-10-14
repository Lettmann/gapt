package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import BetaReduction._
import at.logic.gapt.proofs.SequentIndex

object applySubstitution {
  /**
   * Applies a substitution to an LKProof.
   *
   * @param substitution The substitution to be applied.
   * @param preserveEigenvariables  If true, preserve eigenvariables and never change them.  If false (the default),
   *                                treat eigenvariables as variables bound by their strong quantifier inferences and
   *                                perform capture-avoiding substitution.
   * @param proof The proof to apply the substitution to.
   * @return The substituted proof.
   */
  def apply( substitution: Substitution, preserveEigenvariables: Boolean = false )( proof: LKProof ): LKProof = proof match {
    case InitialSequent( sequent ) =>
      Axiom( sequent.map { f => betaNormalize( substitution( f ) ) } )

    case WeakeningLeftRule( subProof, f ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      WeakeningLeftRule( subProofNew, betaNormalize( substitution( f ) ) )

    case WeakeningRightRule( subProof, f ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      WeakeningRightRule( subProofNew, betaNormalize( substitution( f ) ) )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      ContractionLeftRule( subProofNew, aux1, aux2 )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      ContractionRightRule( subProofNew, aux1, aux2 )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution, preserveEigenvariables )( leftSubProof ), apply( substitution, preserveEigenvariables )( rightSubProof ) )
      CutRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case NegLeftRule( subProof, aux ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      NegLeftRule( subProofNew, aux )

    case NegRightRule( subProof, aux ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      NegRightRule( subProofNew, aux )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      AndLeftRule( subProofNew, aux1, aux2 )

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution, preserveEigenvariables )( leftSubProof ), apply( substitution, preserveEigenvariables )( rightSubProof ) )
      AndRightRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution, preserveEigenvariables )( leftSubProof ), apply( substitution, preserveEigenvariables )( rightSubProof ) )
      OrLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case OrRightRule( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      OrRightRule( subProofNew, aux1, aux2 )

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution, preserveEigenvariables )( leftSubProof ), apply( substitution, preserveEigenvariables )( rightSubProof ) )
      ImpLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      ImpRightRule( subProofNew, aux1, aux2 )

    case ForallLeftRule( subProof, aux, f, term, v ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      val All( newV, newF ) = substitution( All( v, f ) )
      ForallLeftRule( subProofNew, aux, betaNormalize( newF ), betaNormalize( substitution( term ) ), newV )

    case ForallRightRule( subProof, aux, eigen, quant ) if substitution.range contains eigen =>
      require( !preserveEigenvariables, s"Cannot apply substitution: Eigenvariable $eigen is in range of substitution" )
      val renamedEigen = rename( eigen, substitution.range )
      apply( substitution, preserveEigenvariables )( ForallRightRule(
        apply( Substitution( eigen -> renamedEigen ), preserveEigenvariables )( subProof ),
        aux, renamedEigen, quant
      ) )

    case p @ ForallRightRule( subProof, aux, eigen, quant ) =>
      val All( newQuant, _ ) = Substitution( substitution.map - eigen )( p.mainFormula )
      ForallRightRule( apply( Substitution( substitution.map - eigen ) )( subProof ), aux, eigen, newQuant )

    case ExistsLeftRule( subProof, aux, eigen, quant ) if substitution.range contains eigen =>
      require( !preserveEigenvariables, s"Cannot apply substitution: Eigenvariable $eigen is in range of substitution" )
      val renamedEigen = rename( eigen, substitution.range )
      renamedEigen -> apply( Substitution( eigen -> renamedEigen ), preserveEigenvariables )( subProof )
      apply( substitution, preserveEigenvariables )( ExistsLeftRule(
        apply( Substitution( eigen -> renamedEigen ), preserveEigenvariables )( subProof ),
        aux, renamedEigen, quant
      ) )

    case p @ ExistsLeftRule( subProof, aux, eigen, quant ) =>
      val Ex( newQuant, _ ) = Substitution( substitution.map - eigen )( p.mainFormula )
      ExistsLeftRule( apply( Substitution( substitution.map - eigen ) )( subProof ), aux, eigen, newQuant )

    case ExistsRightRule( subProof, aux, f, term, v ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      val Ex( newV, newF ) = substitution( Ex( v, f ) )
      ExistsRightRule( subProofNew, aux, betaNormalize( newF ), betaNormalize( substitution( term ) ), newV )

    case EqualityLeftRule( subProof, eq, aux, pos ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      EqualityLeftRule( subProofNew, eq, aux, pos )

    case EqualityRightRule( subProof, eq, aux, pos ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      EqualityRightRule( subProofNew, eq, aux, pos )

    case InductionRule( leftSubProof, aux1, rightSubProof, aux2, aux3, term ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution, preserveEigenvariables )( leftSubProof ), apply( substitution, preserveEigenvariables )( rightSubProof ) )
      InductionRule( leftSubProofNew, aux1, rightSubProofNew, aux2, aux3, betaNormalize( substitution( term ) ).asInstanceOf[FOLTerm] )

    case DefinitionLeftRule( subProof, aux, main ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      DefinitionLeftRule( subProofNew, aux, betaNormalize( substitution( main ) ) )

    case DefinitionRightRule( subProof, aux, main ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      DefinitionRightRule( subProofNew, aux, betaNormalize( substitution( main ) ) )

    case _ => throw new IllegalArgumentException( s"This rule is not handled at this time." )
  }
}