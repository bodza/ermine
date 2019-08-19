(defproject ermine "x.y.z"
    :dependencies [[org.clojure/clojure "1.10.0"]
                   [fast-zip "0.7.0"]
                   [org.bituf/clj-stringtemplate "0.2"]
                   [org.clojars.amit/commons-io "1.4.0"]
                   [commons-lang "2.5"]
                   [org.flatland/ordered "1.5.7"]
                  ]
    :repl-options {:host "0.0.0.0"
                   :port 7888
                   :init-ns ermine.core}
    :source-paths ["."]
    :main ermine.core
    :aliases {"ermine" ["run" "-m" "ermine.core"]})
