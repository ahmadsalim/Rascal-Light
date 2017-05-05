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

organization := "com.github.itu-square"
organizationName := "SQUARE @ IT University of Copenhagen"
organizationHomepage := Some(url("https://github.com/models-team"))

scalaVersion := "2.12.1"

resolvers += Resolver.sonatypeRepo("releases")

libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.2.9"
libraryDependencies += "co.fs2" %% "fs2-core" % "0.9.4"
libraryDependencies += "org.bitbucket.inkytonik.kiama" %% "kiama" % "2.0.0"

libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.1"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.1" % "test"

addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.3")
