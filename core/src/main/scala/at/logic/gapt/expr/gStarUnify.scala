package at.logic.gapt.expr

/**
 * Created by root on 14.12.16.
 */

/*
Some test code:

import at.logic.gapt.expr.gStarUnify

val nameOfUniversalVariable = fov"x"
val nameOfExistentialVariable = fov"y"
val c = foc"c"
val a = foc"a"
val fc = fot"f($c)"
val ffc = fot"f($fc)"
val fa = fot"f($a)"
val P1 = foa"P($fc,$c,$ffc)"
val P2 = foa"P($a,$c,$fa)"
val P3 = foa"Q($a,$c)"
val NP2 = fof"-$P2"
val setOfLiterals:Set[FOLFormula]=Set(P1,NP2,P3)
val productionRulesX:Set[(LambdaExpression,LambdaExpression)]=Set((fc,a))
val productionRulesY:Set[(LambdaExpression,LambdaExpression)]=Set()
gStarUnify(setOfLiterals,productionRulesX,productionRulesY,nameOfExistentialVariable,nameOfUniversalVariable)


val nameOfUniversalVariable = fov"x"
val nameOfExistentialVariable = fov"y"
val c = foc"c"
val a = foc"a"
val fc = fot"f($c)"
val ffc = fot"f($fc)"
val fa = fot"f($a)"
val P1 = foa"P($fc,$c,$ffc)"
val P2 = foa"P($a,$c,$fa)"
val P3 = foa"Q($a,$c)"
val P4 = foa"Q($a,$c,$fc)"
val NP2 = fof"-$P2"
val NP4 = fof"-$P4"
val setOfLiterals:Set[FOLFormula]=Set(P1,NP2,P3,NP4)
val productionRulesX:Set[(LambdaExpression,LambdaExpression)]=Set((fc,a))
val productionRulesY:Set[(LambdaExpression,LambdaExpression)]=Set((c,c))
gStarUnify(setOfLiterals,productionRulesX,productionRulesY,nameOfExistentialVariable,nameOfUniversalVariable)


val nameOfUniversalVariable = fov"x"
val nameOfExistentialVariable = fov"y"
val c = foc"c"
val a = foc"a"
val fc = fot"f($c)"
val ffc = fot"f($fc)"
val fa = fot"f($a)"
val P1 = foa"P($fc,$c,$ffc)"
val P2 = foa"P($a,$c,$fa)"
val P3 = foa"Q($a,$c)"
val P4 = foa"Q($a,$c)"
val NP2 = fof"-$P2"
val NP4 = fof"-$P4"
val setOfLiterals:Set[FOLFormula]=Set(P1,NP2,P3,NP4)
val productionRulesX:Set[(LambdaExpression,LambdaExpression)]=Set((fc,a))
val productionRulesY:Set[(LambdaExpression,LambdaExpression)]=Set((c,c))
gStarUnify(setOfLiterals,productionRulesX,productionRulesY,nameOfExistentialVariable,nameOfUniversalVariable)
 */

object gStarUnify {

  def apply(
    setOfLiterals:             Set[FOLFormula],
    productionRulesX:          Set[( LambdaExpression, LambdaExpression )],
    productionRulesY:          Set[( LambdaExpression, LambdaExpression )],
    nameOfExistentialVariable: FOLVar,
    nameOfUniversalVariable:   FOLVar
  ): Set[FOLFormula] = {

    val productionRulesXS: scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )] = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    productionRulesX.foreach( element => {
      val ( elementL, elementR ) = element
      productionRulesXS += ( ( elementL, elementR ) )
      productionRulesXS += ( ( elementR, elementL ) )
    } )

    val productionRulesYS: scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )] = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    productionRulesY.foreach( element => {
      val ( elementL, elementR ) = element
      productionRulesYS += ( ( elementL, elementR ) )
      productionRulesYS += ( ( elementR, elementL ) )
    } )

    val literals = sortAndAtomize( setOfLiterals )
    val ( posAtoms, negAtoms ) = literals

    // println( "literals" )
    // println( literals )
    // println( "posAtoms" )
    // println( posAtoms )
    // println( "negAtoms" )
    // println( negAtoms )

    val unifiedLiterals = scala.collection.mutable.Set[FOLFormula]()

    posAtoms.foreach( posAt =>
      negAtoms.foreach( negAt =>
        unifyLiterals( posAt, negAt, productionRulesXS.toSet, productionRulesYS.toSet, nameOfExistentialVariable, nameOfUniversalVariable ) match {
          /*
          The next line is a compromise since we do not consider negation during the unification procedure (Future work). This way we add some unnecessary literals.
           */
          case Some( t ) => {
            unifiedLiterals += t
            unifiedLiterals += Neg( t )
          }
          case None =>
        } ) )

    unifiedLiterals.toSet

  }

  private def sortAndAtomize( literals: Set[FOLFormula] ): ( Set[FOLFormula], Set[FOLFormula] ) = {

    val posLiterals: scala.collection.mutable.Set[FOLFormula] = scala.collection.mutable.Set()
    val negLiterals: scala.collection.mutable.Set[FOLFormula] = scala.collection.mutable.Set()

    for ( literal <- literals ) {

      literal match {
        case Neg( t ) => negLiterals += t
        case _        => posLiterals += literal
      }

    }

    ( posLiterals.toSet, negLiterals.toSet )

  }

  private def unifyLiterals(
    posAt:                     FOLFormula,
    negAt:                     FOLFormula,
    productionRulesX:          Set[( LambdaExpression, LambdaExpression )],
    productionRulesY:          Set[( LambdaExpression, LambdaExpression )],
    nameOfExistentialVariable: FOLVar,
    nameOfUniversalVariable:   FOLVar
  ): Option[FOLFormula] = {

    val Apps( nameOfPos, argsP ): FOLFormula = posAt
    val Apps( nameOfNeg, argsN ): FOLFormula = negAt

    val unifiedLiteral: Option[FOLFormula] = nameOfPos match {
      case t if ( ( nameOfNeg == t ) && ( argsP.length == argsN.length ) ) => {
        val unifiedArgs = unify( argsP.zip( argsN ), productionRulesX, productionRulesY, nameOfExistentialVariable, nameOfUniversalVariable )

        // println( "unifiedArgs" )
        // println( unifiedArgs )
        // println( "argsP" )
        // println( argsP )
        // println( "argsN" )
        // println( argsN )
        // println( "productionRulesX" )
        // println( productionRulesX )
        // println( "productionRulesY" )
        // println( productionRulesY )

        val theUnifiedLiteral = unifiedArgs match {
          case Some( s ) => {
            if ( s.length == argsP.length ) {
              Some( Apps( nameOfPos, s ).asInstanceOf[FOLFormula] )
            } else {
              None
            }
          }
          case _ => None
        }
        theUnifiedLiteral
      }
      case _ => None
    }

    // println( "unifiedLiteral" )
    // println( unifiedLiteral )

    unifiedLiteral

  }

  private def unify(
    zippedArgs:                List[( LambdaExpression, LambdaExpression )],
    productionRulesX:          Set[( LambdaExpression, LambdaExpression )],
    productionRulesY:          Set[( LambdaExpression, LambdaExpression )],
    nameOfExistentialVariable: FOLVar,
    nameOfUniversalVariable:   FOLVar
  ): Option[Seq[FOLTerm]] = {

    var unifiedTerms: Option[Seq[FOLTerm]] = None
    var stopIt: Boolean = false
    var stopItAll: Boolean = false
    var iterator: Int = 1

    zippedArgs.foreach( t => {
      stopIt = false
      stopItAll = false

      val ( tL, tR ) = t

      // println( "t" )
      // println( t )
      // println( "productionRulesX.size" )
      // println( productionRulesX.size )

      productionRulesX.foreach( productionRuleX => if ( !stopIt ) {

        val ( productionRuleXL, productionRuleXR ) = productionRuleX

        if ( productionRuleXL.syntaxEquals( tL ) && productionRuleXR.syntaxEquals( tR ) ) {
          unifiedTerms = unifiedTerms match {
            case Some( update ) => Option( update ++: Seq( nameOfUniversalVariable ) )
            case None           => Option( Seq( nameOfUniversalVariable ) )
          }
          stopIt = true
          stopItAll = true
        }

        // println( "comparison" )
        // println( productionRuleXL.syntaxEquals( tL ) && productionRuleXR.syntaxEquals( tR ) )
        // println( "XL" )
        // println( productionRuleXL )
        // println( "tL" )
        // println( tL )
        // println( "XR" )
        // println( productionRuleXR )
        // println( "tR" )
        // println( tR )

        if ( iterator == productionRulesX.size ) {
          iterator = 1
          stopIt = true
        } else {
          iterator += 1
        }
      } )

      stopIt = false

      productionRulesY.foreach( productionRuleY => if ( ( !stopIt ) && ( !stopItAll ) ) {

        val ( productionRuleYL, productionRuleYR ) = productionRuleY

        if ( productionRuleYL.syntaxEquals( tL ) && productionRuleYR.syntaxEquals( tR ) ) {
          unifiedTerms = unifiedTerms match {
            case Some( update ) => Option( update ++: Seq( nameOfExistentialVariable ) )
            case None           => Option( Seq( nameOfExistentialVariable ) )
          }
          stopIt = true
          stopItAll = true
        }

        if ( iterator == productionRulesY.size ) {
          iterator = 1
          stopIt = true
        } else {
          iterator += 1
        }
      } )

      if ( !stopItAll ) {

        val Apps( nameOfArgL, argsOfArgL ) = tL
        val Apps( nameOfArgR, argsOfArgR ) = tR

        if ( tL.syntaxEquals( tR ) ) {

          unifiedTerms = unifiedTerms match {
            case Some( update ) => Option( update ++: Seq( tL.asInstanceOf[FOLTerm] ) )
            case None           => Option( Seq( tR.asInstanceOf[FOLTerm] ) )
          }

        } else if ( ( nameOfArgL == nameOfArgR ) && ( argsOfArgL.length == argsOfArgR.length ) ) {

          unify( argsOfArgL.zip( argsOfArgR ), productionRulesX, productionRulesY, nameOfExistentialVariable, nameOfUniversalVariable ) match {
            case Some( r ) => unifiedTerms = unifiedTerms match {
              case Some( update ) => Option( update ++: Seq( Apps( nameOfArgL, r ).asInstanceOf[FOLTerm] ) )
              case None           => Option( Seq( Apps( nameOfArgL, r ).asInstanceOf[FOLTerm] ) )
            }
            case _ =>
          }

        }
      }

      // println( "unifiedTerms" )
      // println( unifiedTerms )

    } )

    unifiedTerms

  }

}
