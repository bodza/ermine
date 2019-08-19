(defproject ermine "x.y.z"
    :dependencies [[org.clojure/clojure "1.10.0"]
                   [org.clojure/tools.cli "0.4.2"]
                   [org.clojure/tools.logging "0.4.1"]
                   [org.slf4j/slf4j-simple "1.7.25"]
                   [fast-zip "0.7.0"]
                   [clj-jgit "0.8.10"]
                   [org.bituf/clj-stringtemplate "0.2"]
                   [org.clojars.amit/commons-io "1.4.0"]
                   [commons-lang "2.5"]
                   [org.flatland/ordered "1.5.7"]
                   [watchtower "0.1.1"]
                  ]
    :repl-options {:host "0.0.0.0"
                   :port 7888
                   :init-ns compiler.core}
    :source-paths ["src"] :test-paths ["src"]
    :main compiler.core
    :aliases {"ermine" ["run" "-m" "compiler.core"]})
