import com.typesafe.sbt.license.LicenseInfo

resolvers ++= Seq(
  Resolver.sonatypeRepo("releases"),
  Resolver.sonatypeRepo("snapshots")
)

name := "Rascal Light"
description := "Implementation and analyses for a subset of Rascal"
version := "0.1"
startYear := Some(2017)
licenses += (LicenseInfo.BSD2.name, url(LicenseInfo.BSD2.url))

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature")

organization := "com.github.itu-square"
organizationName := "SQUARE @ IT University of Copenhagen"
organizationHomepage := Some(url("https://github.com/itu-square"))

scalaVersion := "2.12.1"

resolvers += Resolver.sonatypeRepo("releases")

libraryDependencies += "com.twitter" %% "util-collection" % "17.11.0"

libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.2.9"
libraryDependencies += "co.fs2" %% "fs2-core" % "0.9.4"
libraryDependencies += "org.bitbucket.inkytonik.kiama" %% "kiama" % "2.0.0"

libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.1"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"
libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.14.0" % "test"

libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3"
libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.7.2"

libraryDependencies += "org.codehaus.groovy" % "groovy-all" % "2.5.8"

addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.3")

testOptions in Test += Tests.Argument("-oD")

cancelable in Global := true
