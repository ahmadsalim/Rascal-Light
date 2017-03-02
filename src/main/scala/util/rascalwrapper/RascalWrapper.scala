package util.rascalwrapper

import java.io.File
import java.nio.file.Files

import org.rascalmpl.library.lang.rascal.syntax.RascalParser
import org.rascalmpl.parser.gtd.result.out.DefaultNodeFlattener
import org.rascalmpl.parser.uptr.UPTRNodeFactory
import org.rascalmpl.values.uptr.ITree

object RascalWrapper {
  def parseRascal(path: String): ITree = {
    val parser = new RascalParser()
    val file = new File(path)
    val input = new String(Files.readAllBytes(file.toPath))
    parser.parse("start__Module", file.toURI(), input.toCharArray, new DefaultNodeFlattener(), new UPTRNodeFactory(/* allowAmbiguity */ false))
  }
}