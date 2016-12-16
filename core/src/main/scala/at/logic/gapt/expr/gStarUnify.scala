package at.logic.gapt.expr

/**
 * Created by root on 14.12.16.
 */

/*
Some test code:
import at.logic.gapt.expr.gStarUnify
val x = fov"x"
val y = fov"y"
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
val nameOfExistentialVariable:LambdaExpression = y
val nameOfUniversalVariable:LambdaExpression = x
gStarUnify(setOfLiterals,productionRulesX,productionRulesY,nameOfExistentialVariable,nameOfUniversalVariable)
 */

object gStarUnify {

  def apply(
    setOfLiterals:             Set[FOLFormula],
    productionRulesX:          Set[( LambdaExpression, LambdaExpression )],
    productionRulesY:          Set[( LambdaExpression, LambdaExpression )],
    nameOfExistentialVariable: LambdaExpression,
    nameOfUniversalVariable:   LambdaExpression
  ): Set[LambdaExpression] = {

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

    val unifiedLiterals = scala.collection.mutable.Set[LambdaExpression]()

    posAtoms.foreach( posAt =>
      negAtoms.foreach( negAt =>
        unifyLiterals( posAt, negAt, productionRulesXS.toSet, productionRulesYS.toSet, nameOfExistentialVariable, nameOfUniversalVariable ) match {
          case Some( t ) => unifiedLiterals += t
          case None      =>
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
    nameOfExistentialVariable: LambdaExpression,
    nameOfUniversalVariable:   LambdaExpression
  ): Option[LambdaExpression] = {

    val Apps( nameOfPos, argsP ) = posAt
    val Apps( nameOfNeg, argsN ) = negAt

    val unifiedLiteral: Option[LambdaExpression] = nameOfPos match {
      case t if ( ( nameOfNeg == t ) && ( argsP.length == argsN.length ) ) => {
        val unifiedArgs = unify( argsP.zip( argsN ), productionRulesX, productionRulesY, nameOfExistentialVariable, nameOfUniversalVariable )
        val theUnifiedLiteral = unifiedArgs match {
          case Some( t ) => Some( Apps( nameOfPos, t ) )
          case _         => None
        }
        theUnifiedLiteral
      }
      case _ => None
    }

    unifiedLiteral

  }

  private def unify(
    zippedArgs:                List[( LambdaExpression, LambdaExpression )],
    productionRulesX:          Set[( LambdaExpression, LambdaExpression )],
    productionRulesY:          Set[( LambdaExpression, LambdaExpression )],
    nameOfExistentialVariable: LambdaExpression,
    nameOfUniversalVariable:   LambdaExpression
  ): Option[Seq[LambdaExpression]] = {

    var unifiedTerms: Option[Seq[LambdaExpression]] = None
    var stopIt: Boolean = false
    var iterator: Int = 0

    zippedArgs.foreach( t => {
      stopIt = false
      productionRulesX.foreach( productionRuleX => while ( !stopIt ) {

        t match {
          case pair if ( productionRuleX == pair ) => {
            unifiedTerms = unifiedTerms match {
              case Some( update ) => Option( update ++: Seq( nameOfUniversalVariable ) )
              case None           => Option( Seq( nameOfUniversalVariable ) )
            }
            iterator = productionRulesX.size
          }
          case _ => {
            productionRulesY.foreach( productionRuleY => while ( !stopIt ) {

              t match {
                case pair if ( productionRuleY == pair ) => {
                  unifiedTerms = unifiedTerms match {
                    case Some( update ) => Option( update ++: Seq( nameOfExistentialVariable ) )
                    case None           => Option( Seq( nameOfExistentialVariable ) )
                  }
                  iterator = productionRulesY.size
                }
                case _ => {

                  val ( argL, argR ) = t
                  if ( argL == argR ) {
                    unifiedTerms = unifiedTerms match {
                      case Some( update ) => Option( update ++: Seq( argL ) )
                      case None           => Option( Seq( argL ) )
                    }
                  } else {
                    val Apps( nameOfArgL, argsOfArgL ) = argL
                    val Apps( nameOfArgR, argsOfArgR ) = argR

                    if ( ( nameOfArgL == nameOfArgR ) && ( argsOfArgL.length == argsOfArgR.length ) ) {
                      unify( argsOfArgL.zip( argsOfArgR ), productionRulesX, productionRulesY, nameOfExistentialVariable, nameOfUniversalVariable ) match {
                        case Some( r ) => unifiedTerms = unifiedTerms match {
                          case Some( update ) => Option( update ++: Seq( Apps( nameOfArgL, r ) ) )
                          case None           => Option( Seq( Apps( nameOfArgL, r ) ) )
                        }
                        case _ => stopIt = true
                      }
                    } else {
                      stopIt = true
                      unifiedTerms = None
                    }
                  }

                }
              }

              if ( iterator == productionRulesY.size ) {
                iterator = 0
                stopIt = true
              } else {
                iterator += 1
              }

            } )
          }
        }

        if ( iterator == productionRulesX.size ) {
          iterator = 0
          stopIt = true
        } else {
          iterator += 1
        }

      } )
    } )

    unifiedTerms

  }

}
