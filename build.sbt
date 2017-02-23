import com.typesafe.sbt.license.{LicenseInfo, DepModuleInfo}

name := "Maverick"
description := "A tool for analyzing core-Rascal programs"
version := "0.1"
startYear := Some(2017)
licenses += (LicenseInfo.BSD2.name, url(LicenseInfo.BSD2.url))

organization := "com.github.models-team"
organizationName := "MODELS Team @ IT University of Copenhagen"
organizationHomepage := Some(url("https://github.com/models-team"))

scalaVersion := "2.12.1"

resolvers += Resolver.sonatypeRepo("releases")

libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.2.9"

addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.3")