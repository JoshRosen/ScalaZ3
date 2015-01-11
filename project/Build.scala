import sbt._
import Keys._

object ScalaZ3build extends Build {


  lazy val root = Project(id = "ScalaZ3",
                          base = file("."),
                          settings = Project.defaultSettings
                     )
}
