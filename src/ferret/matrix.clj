(defn row-count [^matrix u]
  "return obj<number>(matrix::row_count(u));")

(defn column-count [^matrix u]
  "return obj<number>(matrix::column_count(u));")

(defn zeros [^size_t r, ^size_t c]
  "return obj<matrix_t>(matrix::zeros(r, c));")

(defn ones [^size_t r, ^size_t c]
  "return obj<matrix_t>(matrix::ones(r,c));")

(defn full [^size_t r, ^size_t c, ^real_t v]
  "return obj<matrix_t>(matrix::ones(r,c,v));")

(defn eye [^size_t n]
  "return obj<matrix_t>(matrix::eye(n));")

(defn add [^matrix u ^matrix v]
  "return obj<matrix_t>(u + v);")

(defn sub [^matrix u ^matrix v]
  "return obj<matrix_t>(u - v);")

(defn mul [^matrix u ^real_t s]
  "return obj<matrix_t>(u * s);")

(defn mmul [^matrix u ^matrix v]
  "return obj<matrix_t>(u * v);")

(defn equals [^matrix u ^matrix v]
  "if (u == v)
       return cached::true_o;
   else
       return cached::false_o;")

(defn normalise [^matrix u]
  "return obj<matrix_t>(matrix::normalise(u));")

(defn norm [^matrix u]
  "return obj<number>(matrix::norm_euclidean(u));")

(defn mset! [^matrix u ^size_t r ^size_t c ^real_t v]
  "u(r, c, v);")

(defn mget [^matrix u ^size_t r ^size_t c]
  "return obj<number>(u(r, c));")

(defn cout [^matrix u]
  "std::cout << u;")

(defn seq [u]
  "return obj<array_seq<real_t, number>>(u);")
