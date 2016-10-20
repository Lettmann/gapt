package at.logic.gapt.proofs.resolution

import at.logic.gapt.proofs.{ HOLSequent }

import scala.collection.mutable

/** Converts a resolution proof to a Herbrand sequent. */
object ResolutionToDeepFunctionFromProj {

  def apply( proof: ResolutionProof, input: Input => HOLSequent ): HOLSequent = {

    val memo = mutable.Map[ResolutionProof, HOLSequent]()

    def f( p: ResolutionProof ): HOLSequent = memo.getOrElseUpdate( p, p match {
      case in: Input => input( in )
      /*case Taut( formula ) => LogicalAxiom( formula )
      case Refl( term )    => ReflexivityAxiom( term )

      case p @ Defn( defConst, defExpr ) =>
        val phi = BetaReduction.betaNormalize( defExpr( p.vars ) ).asInstanceOf[HOLFormula]
        val definition = Definition( defConst, defExpr )
        val ctx = replacementContext.abstractTerm( defConst( p.vars: _* ) )( defConst )

        ProofBuilder.
          c( LogicalAxiom( phi ) ).
          u( DefinitionLeftRule( _, Ant( 0 ), definition, ctx ) ).
          u( ImpRightRule( _, Ant( 0 ), Suc( 0 ) ) ).
          c( LogicalAxiom( phi ) ).
          u( DefinitionRightRule( _, Suc( 0 ), definition, ctx ) ).
          u( ImpRightRule( _, Ant( 0 ), Suc( 0 ) ) ).
          b( AndRightRule( _, Suc( 0 ), _, Suc( 0 ) ) ).
          u( ForallRightBlock( _, p.definitionFormula, p.vars ) ).
          qed

      case Factor( q, i1, i2 ) =>
        if ( i1 isAnt )
          ContractionLeftRule( f( q ), q.conclusion( i1 ) )
        else
          ContractionRightRule( f( q ), q.conclusion( i1 ) ) */
      case Resolution( q1, i1, q2, i2 ) =>
        ( f( q1 ) ++ f( q2 ) ).distinct
      case Subst( q, subst ) =>
        subst( f( q ) )
      /*case p @ Paramod( q1, i1, ltr, q2, i2, ctx: Abs ) =>
        if ( i2 isAnt )
          ParamodulationLeftRule( f( q1 ), q1.conclusion( i1 ), f( q2 ), q2.conclusion( i2 ), ctx )
        else
          ParamodulationRightRule( f( q1 ), q1.conclusion( i1 ), f( q2 ), q2.conclusion( i2 ), ctx )

      case p @ AvatarContradiction( q ) => f( q )
      case AvatarComponent( comp @ AvatarNonGroundComp( splAtom, aux, vars ) ) =>
        val \/-( p1 ) = solvePropositional( comp.disjunction +: comp.clause )
        val p2 = ForallLeftBlock( p1, aux, vars )

        val p3 = DefinitionLeftRule( p2, aux, comp.toDefinition, splAtom )
        p3
      case AvatarComponent( AvatarGroundComp( atom, _ ) ) => LogicalAxiom( atom )
      case AvatarComponent( comp @ AvatarNegNonGroundComp( splAtom, aux, vars, idx ) ) =>
        val \/-( p1 ) = solvePropositional( comp.clause :+ comp.disjunction )
        val p2 = ForallRightBlock( p1, aux, vars )
        val p3 = DefinitionRightRule( p2, aux, comp.toDefinition, splAtom )
        p3
      case AvatarSplit( q, indices, AvatarGroundComp( _, _ ) ) => f( q )
      case p @ AvatarSplit( q, _, comp @ AvatarNonGroundComp( splAtom, aux, vars ) ) =>
        var p_ = f( q )
        for {
          a <- comp.clause.antecedent
          if p_.conclusion.antecedent contains a
        } p_ = NegRightRule( p_, a )
        def mkOr( lits: HOLFormula ): Unit =
          lits match {
            case Or( lits_, lit ) =>
              mkOr( lits_ )
              p_ = OrRightMacroRule( p_, lits_, lit )
            case lit =>
              if ( !p_.conclusion.succedent.contains( lit ) )
                p_ = WeakeningRightRule( p_, lit )
          }
        mkOr( comp.disjunction )
        p_ = ForallRightBlock( p_, aux, vars )
        p_ = DefinitionRightRule( p_, aux, comp.toDefinition, splAtom )
        p_

      case DefIntro( q, i: Suc, definition, args ) =>
        val Definition( what, by ) = definition
        val tp = what.exptype
        val X = rename awayFrom freeVariables( args ) fresh Var( "X", tp )
        val ctx = Abs( X, Apps( X, args ) )
        DefinitionRightRule( f( q ), q.conclusion( i ), definition, ctx )

      case DefIntro( q, i: Ant, definition, args ) =>
        val Definition( what, by ) = definition
        val tp = what.exptype
        val X = rename awayFrom freeVariables( args ) fresh Var( "X", tp )
        val ctx = Abs( X, Apps( X, args ) )
        DefinitionLeftRule( f( q ), q.conclusion( i ), definition, ctx )

      case p @ Flip( q, i: Ant ) =>
        CutRule( mkSymmProof( p.s, p.t ), f( q ), q.conclusion( i ) )
      case p @ Flip( q, i: Suc ) =>
        CutRule( f( q ), mkSymmProof( p.t, p.s ), q.conclusion( i ) )

      case p: TopL    => reducef( p ) { _ => TopAxiom }
      case p: BottomR => reducef( p ) { _ => BottomAxiom }
      case p: NegL    => reducef( p ) { case Neg( l ) => NegRightRule( LogicalAxiom( l ), Ant( 0 ) ) }
      case p: NegR    => reducef( p ) { case Neg( l ) => NegLeftRule( LogicalAxiom( l ), Suc( 0 ) ) }
      case p: AndL    => reducef( p ) { case And( l, r ) => AndRightRule( LogicalAxiom( l ), Suc( 0 ), LogicalAxiom( r ), Suc( 0 ) ) }
      case p: AndR1   => reducef( p ) { case And( l, r ) => AndLeftRule( WeakeningLeftRule( LogicalAxiom( l ), r ), Ant( 1 ), Ant( 0 ) ) }
      case p: AndR2   => reducef( p ) { case And( l, r ) => AndLeftRule( WeakeningLeftRule( LogicalAxiom( r ), l ), Ant( 0 ), Ant( 1 ) ) }
      case p: OrR     => reducef( p ) { case Or( l, r ) => OrLeftRule( LogicalAxiom( l ), Ant( 0 ), LogicalAxiom( r ), Ant( 0 ) ) }
      case p: OrL1    => reducef( p ) { case Or( l, r ) => OrRightRule( WeakeningRightRule( LogicalAxiom( l ), r ), Suc( 0 ), Suc( 1 ) ) }
      case p: OrL2    => reducef( p ) { case Or( l, r ) => OrRightRule( WeakeningRightRule( LogicalAxiom( r ), l ), Suc( 1 ), Suc( 0 ) ) }
      case p: ImpR    => reducef( p ) { case Imp( l, r ) => ImpLeftRule( LogicalAxiom( l ), Suc( 0 ), LogicalAxiom( r ), Ant( 0 ) ) }
      case p: ImpL1   => reducef( p ) { case Imp( l, r ) => ImpRightRule( WeakeningRightRule( LogicalAxiom( l ), r ), Ant( 0 ), Suc( 1 ) ) }
      case p: ImpL2   => reducef( p ) { case Imp( l, r ) => ImpRightRule( WeakeningLeftRule( LogicalAxiom( r ), l ), Ant( 0 ), Suc( 0 ) ) }

      case p: AllL    => reducef( p )( f => ForallSkRightRule( LogicalAxiom( instantiate( f, p.skolemTerm ) ), Suc( 0 ), f, p.skolemTerm, p.skolemDef ) )
      case p: ExR     => reducef( p )( f => ExistsSkLeftRule( LogicalAxiom( instantiate( f, p.skolemTerm ) ), Ant( 0 ), f, p.skolemTerm, p.skolemDef ) )

      case p: AllR    => reducef( p )( f => ForallLeftRule( LogicalAxiom( instantiate( f, p.variable ) ), f, p.variable ) )
      case p: ExL     => reducef( p )( f => ExistsRightRule( LogicalAxiom( instantiate( f, p.variable ) ), f, p.variable ) )
    */
    } )
    f( proof )
  }
}
