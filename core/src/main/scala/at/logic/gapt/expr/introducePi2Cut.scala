package at.logic.gapt.expr

import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.proofs.{ FOLClause, Sequent }

/**
 * Created by root on 09.01.17.
 */

/*
val x = fov"x"
val y = fov"y"
val tX = fot"t($x)"
val r = fot"r"
val Px = fof"P($x,$tX)"
val Py = fof"P($r,$y)"
val R = Px +: Sequent() :+ Py
val seHs = new pi2SeHs(R,x,List(y),List(r),List(tX))
seHs.multiplicityOfAlpha
seHs.multiplicityOfBeta
seHs.substitutionPairsAlpha
seHs.substitutionPairsBetaI(1)
seHs.substitutionPairsBeta
seHs.substitutionsAlpha
seHs.substitutionsBetaI(1)
seHs.herbrandSequent

val x = fov"x"
val y1 = fov"y2"
val y2 = fov"y1"
val tX = fot"t($x)"
val r = fot"r"
val Px = fof"P($x,$tX)"
val Py1 = fof"P($r,$y1)"
val R = Px +: Sequent() :+ Py1
val seHs = new pi2SeHs(R,x,List(y1,y2),List(r),List(tX))

val x = fov"x"
val y1 = fov"y1"
val y2 = fov"y2"
val t1X = fot"t1($x)"
val t2X = fot"t2($x)"
val t3X = fot"t3($x)"
val r1 = fot"r1"
val r2 = fot"r2($y1)"
val Px1 = fof"P($x,$t1X)"
val Px2 = fof"P($x,$t2X)"
val Px3 = fof"P($x,$t3X)"
val Py1 = fof"P($r1,$y1)"
val Py2 = fof"P($r2,$y2)"
val F = fof"$Px1|$Px2|$Px3"
val R = F +: Sequent() :+ Py2 :+ Py1
val seHs = new pi2SeHs(R,x,List(y1,y2),List(r1,r2),List(t1X,t2X,t3X))
seHs.multiplicityOfAlpha
seHs.multiplicityOfBeta
seHs.substitutionPairsAlpha
seHs.substitutionPairsBetaI(1)
seHs.substitutionPairsBeta
seHs.substitutionsAlpha
seHs.substitutionsBetaI(1)
seHs.herbrandSequent
seHs.reducedRepresentationToFormula

val x = fov"x"
val y = fov"y"
val z = fov"z"
val r1 = fot"r1"
val r2 = fot"r2($y)"
val t1 = fot"t1($x)"
val t2 = fot"t2($x)"
val ft1 = fot"f($t1)"
val ft2 = fot"f($t2)"
val fy = fot"f($y)"
val fz = fot"f($z)"
val sx = fot"s($x)"
val sr1 = fot"s($r1)"
val sr2 = fot"s($r2)"
val P1 = fof"P($x,$ft1)"
val P2 = fof"P($x,$ft2)"
val P3 = fof"P($r1,$fy)"
val P4 = fof"P($r2,$fz)"
val Q1 = fof"Q($sx,$t1)"
val Q2 = fof"Q($sx,$t2)"
val Q3 = fof"Q($sr1,$y)"
val Q4 = fof"Q($sr2,$z)"
val F = fof"$P1|$Q1|$P2|$Q2"
val G1 = fof"$P3|$Q3"
val G2 = fof"$P4|$Q4"
val G = fof"$G1&$G2"
val R = F +: Sequent() :+ G
val seHs = new pi2SeHs(R,x,List(y,z),List(r1,r2),List(t1,t2))


import at.logic.gapt.expr.introducePi2Cut
val xName = fov"xName"
val yName = fov"yName"
introducePi2Cut(seHs,yName,xName)
 */

class pi2SeHs(
    reRe: Sequent[FOLFormula], // F[x\U_1] |- G[y\U_2]
    unEi: FOLVar, // alpha
    exEi: List[FOLVar], // beta_1,...,beta_m
    suA:  List[LambdaExpression], // r_1,...,r_m
    suBA: List[LambdaExpression] // t_1(alpha),...,t_p(alpha)
) {

  require( exEi.length == suA.length )

  val multiplicityOfAlpha: Int = suA.length // m
  val multiplicityOfBeta: Int = suBA.length // p
  val reducedRepresentation: Sequent[FOLFormula] = reRe
  val universalEigenvariable: FOLVar = unEi
  val existentialEigenvariables: List[FOLVar] = exEi
  val substitutionsForAlpha: List[LambdaExpression] = suA
  val substitutionsForBetaWithAlpha: List[LambdaExpression] = suBA
  var balancedSolution: Option[FOLFormula] = None
  var noSolutionHasBeenFound: Boolean = true

  // (alpha,r_1),...,(alpha,r_m)
  //////////////////////////////
  def substitutionPairsAlpha(): Set[( LambdaExpression, LambdaExpression )] = {

    val substitutionPairsAlpha = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    substitutionsForAlpha.foreach( instance => {
      val buffer: ( LambdaExpression, LambdaExpression ) = ( universalEigenvariable, instance )
      substitutionPairsAlpha += buffer
    } )
    substitutionPairsAlpha.toSet
  }

  // (beta_i,t_1(alpha)),...,(beta_i,t_p(alpha))
  //////////////////////////////////////////////
  def substitutionPairsBetaI( index: Int ): Set[( LambdaExpression, LambdaExpression )] = {

    val substitutionPairsBetaI = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    substitutionsForBetaWithAlpha.foreach( instanceB => {
      val buffer: ( LambdaExpression, LambdaExpression ) = ( existentialEigenvariables( index - 1 ), instanceB )
      substitutionPairsBetaI += buffer
    } )
    substitutionPairsBetaI.toSet
  }

  // (beta_1,t_1(alpha)),...,(beta_1,t_p(alpha)),
  //                     ...                    ,
  // (beta_m,t_1(alpha)),...,(beta_m,t_p(alpha))
  ///////////////////////////////////////////////
  def substitutionPairsBeta(): Set[( LambdaExpression, LambdaExpression )] = {

    val substitutionPairsBeta = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    for ( index <- 1 to multiplicityOfAlpha ) {
      substitutionPairsBeta ++= substitutionPairsBetaI( multiplicityOfAlpha - index + 1 )
    }
    substitutionPairsBeta.toSet
  }

  // (alpha->r_1),...,(alpha->r_m)
  ////////////////////////////////
  def substitutionsAlpha(): List[Substitution] = {

    val substitutionsAlpha = scala.collection.mutable.ListBuffer[Substitution]()
    substitutionsForAlpha.foreach( instanceA => {
      substitutionsAlpha += Substitution( universalEigenvariable, instanceA )
    } )
    substitutionsAlpha.toList
  }

  // (beta_i->t_1(r_i)),...,(beta_i->t_p(r_i))
  ////////////////////////////////////////////
  def substitutionsBetaI( index: Int ): List[Substitution] = {

    val substitutionsBeta = scala.collection.mutable.ListBuffer[Substitution]()
    val subs: Substitution = Substitution( universalEigenvariable, substitutionsForAlpha( index - 1 ) ) // (alpha->r_i)
    substitutionsForBetaWithAlpha.foreach( instanceB => {
      substitutionsBeta += Substitution( existentialEigenvariables( index - 1 ), subs( instanceB ) )
    } )
    substitutionsBeta.toList
  }

  private def substituteRightSideOnce( sequent: Sequent[HOLFormula], index: Int ): Sequent[HOLFormula] = {

    var resultingSequent: Sequent[HOLFormula] = Sequent()

    sequent.succedent.foreach( formula => {
      formula.find( existentialEigenvariables( index - 1 ) ) match {
        case List() => resultingSequent = resultingSequent :+ formula
        case _ => substitutionsBetaI( index ).foreach( subs => {
          resultingSequent = resultingSequent :+ subs( formula )
        } )
      }
    } )

    resultingSequent
  }

  private def substituteLeftSideOnce( sequent: Sequent[HOLFormula], index: Int ): Sequent[HOLFormula] = {

    var resultingSequent: Sequent[HOLFormula] = Sequent()

    sequent.antecedent.foreach( formula => {
      formula.find( existentialEigenvariables( index - 1 ) ) match {
        case List() => resultingSequent = formula +: resultingSequent
        case _ => substitutionsBetaI( index ).foreach( subs => {
          resultingSequent = subs( formula ) +: resultingSequent
        } )
      }
    } )

    resultingSequent
  }

  // F[x\T_1] |- G[y\T_2]
  ///////////////////////
  def herbrandSequent(): Sequent[HOLFormula] = {

    var herbrandSequent: Sequent[HOLFormula] = Sequent() :++ reducedRepresentation.succedent

    for ( indexM <- 0 until multiplicityOfAlpha ) {
      herbrandSequent = substituteRightSideOnce( herbrandSequent, multiplicityOfAlpha - indexM )
    }

    reducedRepresentation.antecedent.foreach( formula => {
      substitutionsForAlpha.foreach( instanceA => {
        val subs: Substitution = Substitution( universalEigenvariable, instanceA )
        herbrandSequent = subs( formula ) +: herbrandSequent
      } )
    } )

    val sequent: Sequent[HOLFormula] = herbrandSequent

    for ( indexM <- 0 until multiplicityOfAlpha ) {
      herbrandSequent = substituteLeftSideOnce( sequent.antecedent ++: Sequent(), multiplicityOfAlpha - indexM ) :++ sequent.succedent
    }

    herbrandSequent
  }

  // The reduced representation as a formula
  ////////////////////////////////////////
  def reducedRepresentationToFormula(): FOLFormula = {

    var antecedentO: FOLFormula = Top()
    var succedentO: FOLFormula = Bottom()

    reducedRepresentation.antecedent.foreach( formula => antecedentO = fof"$antecedentO & $formula" )
    reducedRepresentation.succedent.foreach( formula => succedentO = fof"$succedentO | $formula" )

    val formula: FOLFormula = fof"$antecedentO->$succedentO"

    formula
  }
}

object introducePi2Cut {

  def apply(
    seHs:                      pi2SeHs,
    nameOfExistentialVariable: FOLVar,
    nameOfUniversalVariable:   FOLVar
  ): Option[FOLFormula] = {

    val literals = scala.collection.mutable.Set[FOLFormula]()
    val DNTA = scala.collection.mutable.Set[Sequent[FOLFormula]]()

    CNFp( seHs.reducedRepresentationToFormula() ).foreach( clause => if ( !clause.isTaut ) {
      var NTAClause: Sequent[FOLFormula] = clause
      for ( literal <- clause.succedent ) {
        NTAClause = Neg( literal ) +: NTAClause
      }
      NTAClause = NTAClause.antecedent ++: Sequent()
      DNTA += NTAClause
      clause.antecedent.foreach( atom => literals += atom )
      clause.succedent.foreach( atom => literals += Neg( atom ) )
    } )

    val DNTAList = DNTA.toList

    // println( "DNTAList" )
    // println( DNTAList )
    // println( "literals" )
    // println( literals )
    // println( "seHs.substitutionPairsAlpha" )
    // println( seHs.substitutionPairsAlpha() )
    // println( "seHs.substitutionsPairsBeta" )
    // println( seHs.substitutionPairsBeta() )

    /*
    *** Add to the program ***
    Test whether the names of the variables are already taken.
     */

    val unifiedLiterals: Set[FOLFormula] = gStarUnify(
      literals.toSet,
      seHs.substitutionPairsAlpha(),
      seHs.substitutionPairsBeta(),
      nameOfExistentialVariable,
      nameOfUniversalVariable
    )

    // println( "unifiedLiterals" )
    // println( unifiedLiterals )

    val allowedClausesIndex: ( List[( Set[FOLFormula], List[Int], List[( Int, List[Int] )] )] ) = allowedClausesWithIndex(
      unifiedLiterals,
      DNTAList,
      seHs,
      nameOfUniversalVariable,
      nameOfExistentialVariable
    )

    // println( "allowedClausesIndex" )
    // println( allowedClausesIndex )
    // println( "seHs.noSolutionHasBeenFound" )
    // println( seHs.noSolutionHasBeenFound )

    if ( seHs.noSolutionHasBeenFound ) {
      for ( subsetSize <- 1 to allowedClausesIndex.length; if ( seHs.noSolutionHasBeenFound ) ) {
        for ( subset <- allowedClausesIndex.toSet.subsets( subsetSize ); if ( seHs.noSolutionHasBeenFound ) ) {
          if ( checkCombinedClauses( DNTAList.length, subset.toList ) ) {
            seHs.noSolutionHasBeenFound = false
            val ( clauses, _, _ ) = subset.toList.unzip3
            val clausesAsFormula = clauses.map( clause => clause.toList ).map( clause => ( clause.head /: clause.tail )( And( _, _ ) ) )

            // println( "clausesAsFormula" )
            // println( clausesAsFormula )

            seHs.balancedSolution = Option( ( clausesAsFormula.head /: clausesAsFormula.tail )( Or( _, _ ) ) )

            // println( "seHs.balancedSolution" )
            // println( seHs.balancedSolution )
          }
        }
      }
    }

    if ( !seHs.noSolutionHasBeenFound ) {
      seHs.balancedSolution
    } else {
      None
    }

  }

  private def allowedClausesWithIndex(
    literals:              Set[FOLFormula],
    nonTautologicalLeaves: List[Sequent[FOLFormula]],
    seHs:                  pi2SeHs,
    x:                     FOLVar,
    y:                     FOLVar
  ): ( List[( Set[FOLFormula], List[Int], List[( Int, List[Int] )] )] ) = {

    var clausesPlusIndex = scala.collection.mutable.Set[( Set[FOLFormula], List[Int], List[( Int, List[Int] )] )]()
    val literalsBuffer = scala.collection.mutable.Set( literals.toList: _* )

    clausesPlusIndex = recursionAllowedClausesWithIndex( 1, literalsBuffer, clausesPlusIndex, nonTautologicalLeaves, seHs, x, y )

    clausesPlusIndex.toList
  }

  private def recursionAllowedClausesWithIndex(
    subsetSize:            Int,
    literals:              scala.collection.mutable.Set[FOLFormula],
    clausesPlusIndex:      scala.collection.mutable.Set[( Set[FOLFormula], List[Int], List[( Int, List[Int] )] )],
    nonTautologicalLeaves: List[Sequent[FOLFormula]],
    seHs:                  pi2SeHs,
    x:                     FOLVar,
    y:                     FOLVar
  ): ( scala.collection.mutable.Set[( Set[FOLFormula], List[Int], List[( Int, List[Int] )] )] ) = {

    for ( subset <- literals.subsets( subsetSize ); if seHs.noSolutionHasBeenFound ) {

      var exists = List[Int]()
      var indexList = List[( Int, List[Int] )]()

      for ( leaf <- nonTautologicalLeaves ) {

        for ( existsIndex <- 0 until seHs.multiplicityOfBeta ) {

          val subs: Substitution = Substitution( ( x, seHs.universalEigenvariable ), ( y, seHs.substitutionsForBetaWithAlpha( existsIndex ) ) )
          var subsetSequent: Sequent[FOLFormula] = Sequent()
          for ( ele <- subset ) {
            subsetSequent = subs( ele ).asInstanceOf[FOLFormula] +: subsetSequent
          }

          if ( subsetSequent.isSubsetOf( leaf ) ) {
            exists = exists :+ nonTautologicalLeaves.indexOf( leaf )
          }
        }

        var betaIndexSet = List[Int]()
        for ( forallIndex <- 0 until seHs.multiplicityOfAlpha ) {

          val subs: Substitution = Substitution( ( x, seHs.substitutionsForAlpha( forallIndex ) ), ( y, seHs.existentialEigenvariables( forallIndex ) ) )
          var subsetSequent: Sequent[FOLFormula] = Sequent()
          for ( ele <- subset ) {
            subsetSequent = Neg( subs( ele ).asInstanceOf[FOLFormula] ) +: subsetSequent
          }

          if ( !leaf.intersect( subsetSequent ).isEmpty ) {
            betaIndexSet = betaIndexSet :+ forallIndex
          }

          // println( "leaf.intersect( subsetSequent )" )
          // println( leaf.intersect( subsetSequent ) )
          // println( "subs" )
          // println( subs )
          // println( "subsetSequent" )
          // println( subsetSequent )
        }
        if ( betaIndexSet.nonEmpty ) {
          val newElement: ( Int, List[Int] ) = ( nonTautologicalLeaves.indexOf( leaf ), betaIndexSet )
          indexList = indexList :+ newElement
        }
      }

      // Collects all necessary information and deletes unnecessary literals
      //////////////////////////////////////////////////////////////////////
      if ( exists.nonEmpty ) {
        val clausePlusIndex = ( subset.toSet, exists, indexList )
        clausesPlusIndex += clausePlusIndex
      } else {
        subset.foreach( literal => literals -= literal )
      }

      // Checks whether a single clause is already a solution
      ////////////////////////////////////////////////
      if ( exists.nonEmpty ) {

        var existsIndex: Boolean = true
        val ( i, _ ) = indexList.unzip

        for ( leafIndex <- 0 until nonTautologicalLeaves.length; if existsIndex ) {
          if ( !i.contains( leafIndex ) || !exists.contains( leafIndex ) ) {
            existsIndex = false
          }
        }

        if ( existsIndex ) {

          seHs.noSolutionHasBeenFound = false

          for ( literal <- subset ) {
            val start = seHs.balancedSolution match {
              case Some( t ) => t
              case None      => Top()
            }
            seHs.balancedSolution = Option( And( start, literal ) )
          }
        }

      }

    }

    if ( literals.toList.length <= subsetSize ) {
      clausesPlusIndex
    } else if ( !seHs.noSolutionHasBeenFound ) {
      clausesPlusIndex
    } else {
      recursionAllowedClausesWithIndex( subsetSize + 1, literals, clausesPlusIndex, nonTautologicalLeaves, seHs, x, y )
    }
  }

  private def checkCombinedClauses(
    numberOfDNTAs:             Int,
    setOfClausesPlusIndexSets: List[( Set[FOLFormula], List[Int], List[( Int, List[Int] )] )]
  ): ( Boolean ) = {

    var isSolution: Boolean = true

    val ( _, existsIndexList, betaIndexList ) = setOfClausesPlusIndexSets.unzip3

    for ( i <- 0 until numberOfDNTAs; if isSolution ) {
      if ( !existsIndexList.flatten.toSet.contains( i ) ) {
        isSolution = false
      }
    }

    if ( isSolution ) {
      var list: List[Int] = Nil
      for ( i <- 0 until numberOfDNTAs ) {
        list = list :+ i
      }
      val intersections = new Array[List[Int]]( numberOfDNTAs )
      isSolution = betaIndexList.forall( element => {
        element.forall( ele => {
          val ( leafIndex, satisfiedOnes ) = ele
          var foundEmptyIntersection: Boolean = false
          if ( foundEmptyIntersection ) {
            false
          } else if ( list.contains( leafIndex ) ) {
            list = list.filterNot( t => t == leafIndex )
            intersections( leafIndex ) = satisfiedOnes
            if ( intersections( leafIndex ).isEmpty ) {
              foundEmptyIntersection = true
              false
            } else {
              true
            }
          } else {
            intersections( leafIndex ) = intersections( leafIndex ).intersect( satisfiedOnes )
            if ( intersections( leafIndex ).isEmpty ) {
              foundEmptyIntersection = true
              false
            } else {
              true
            }
          }
        } )
      } )
    }

    isSolution

  }

}
