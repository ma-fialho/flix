package ca.uwaterloo.flix.tools.pkg

import java.net.URL

case class Pkg(name: String,
               version: Version,
               license: String,
               website: URL,
               keywords: List[String],
               categories: List[String],
               description: String,
               authors: List[Author])
