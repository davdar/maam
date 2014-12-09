
name := "JSAI"

version := "1.0"

scalaVersion := "2.10.1"

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature", "-language:postfixOps", "-language:implicitConversions")//, "-Xdisable-assertions")

// ScalaTest
libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test"

/* Fixes PatMatch memory warnings */
initialize ~= { _ ⇒
  sys.props("scalac.patmat.analysisBudget") = "off"
}

// Disable parallel execution of tests
parallelExecution in Test := false

// show durations.
testOptions in Test ++= Seq(Tests.Argument("-oD"), Tests.Argument("-l"), Tests.Argument("Concrete"))

