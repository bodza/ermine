(defproject ermine "x.y.z"
    :dependencies [[org.clojure/clojure "1.10.0"]]
    :repl-options {:host "0.0.0.0"
                   :port 7888
                   :init-ns ermine.core}
    :jvm-opts ["-Xss16m"]
    :source-paths ["src"]
    :main ermine.core
    :aliases {"ermine" ["run" "-m" "ermine.core"]})
