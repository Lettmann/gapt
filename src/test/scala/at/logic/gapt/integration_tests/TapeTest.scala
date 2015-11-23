package at.logic.gapt.integration_tests

import at.logic.gapt.formats.xml.{ XMLParser, saveXML }
import at.logic.gapt.proofs.lk.deleteTautologies
import at.logic.gapt.proofs.lkNew._

import at.logic.gapt.formats.tptp.TPTPFOLExporter
import XMLParser._

import at.logic.gapt.provers.prover9._
import at.logic.gapt.formats.llkNew.LatexLLKExporter
import at.logic.gapt.proofs.ceres._

import java.io.File.separator

import org.specs2.mutable._

class TapeTest extends Specification {
  def checkForProverOrSkip = new Prover9Prover().isInstalled must beTrue.orSkip

  sequential
  "The system" should {

    "parse, skolemize, extract and refute the css of the tape proof" in {
      checkForProverOrSkip
      val proofdb = XMLProofDatabaseParser( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ), true )
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = lkOld2New( proofdb.proofs.head._2 )
      val proof_sk = skolemize( regularize( DefinitionElimination( proofdb.Definitions, proof ) ) )
      println( LatexLLKExporter( proof_sk, true ) )

      println( proof_sk )
      val s = StructCreators.extract( proof_sk )

      //println( s"struct: $s" )
      val cs_ = CharacteristicClauseSet( s )
      println( cs_.size )
      val cs = deleteTautologies( cs_ )
      cs.map( x => println( s"Clause: $x" ) )
      val tptp = TPTPFOLExporter.tptp_problem( cs.toList )
      println( s"tptp string:\n$tptp" )
      val writer = new java.io.FileWriter( "target" + separator + "tape-cs.tptp" )
      writer.write( tptp )
      writer.flush
      val projs = Projections( proof_sk )
      cs.map( x => {
        print( s"projection for clause $x " )
        projs.exists( _.endSequent.diff( proof_sk.endSequent ) setEquals x ) match {
          case true =>
            println( " found!" );
          case false =>
            println( " not found!" )
        }
        //cs.asInstanceOf[Set[HOLSequent]].contains( pes ) must beTrue
      } )
      val path = "target" + separator + "tape-sk.xml"

      new Prover9Prover().getRobinsonProof( cs ) match {
        case None      => "" must beEqualTo( "refutation of struct cs in tptp format failed" )
        case Some( _ ) => true must beEqualTo( true )
      }

      saveXML(
        ( "tape-sk", lkNew2Old( proof_sk ) ) ::
          projs.toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", lkNew2Old( p._1 ) ) ),
        ( "cs", cs.toList ) :: Nil, path
      )
      ( new java.io.File( path ) ).exists() must beEqualTo( true )
      ok
    }

    "apply the full CERES method" in {
      checkForProverOrSkip

      //get the proof
      val pdb = XMLProofDatabaseParser( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ), true )
      pdb.proofs.size must beEqualTo( 1 )
      val proof = skolemize( regularize( DefinitionElimination( pdb.Definitions, lkOld2New( pdb.proofs.head._2 ) ) ) )
      val ancf = CERES( proof )
      ( ancf.endSequent multiSetEquals proof.endSequent ) must beTrue

    }

  }
}
