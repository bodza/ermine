(defn deref [a] "return a.cast<deref_i>()->deref();")

(defn assoc [m k v] "return m.cast<map_t>()->assoc(k, v);")
(defn dissoc [m k] "return m.cast<map_t>()->dissoc(k);")

(defn get [m & args] "return m.cast<map_t>()->val_at(args);")

(defn vals [m] "return m.cast<map_t>()->vals();")
(defn keys [m] "return m.cast<map_t>()->keys();")

(defn atom [x] "return obj<atomic>(x)")

(defn swap! [a f & args] "return a.cast<atomic>()->swap(f, args);")
(defn reset! [a x] "return a.cast<atomic>()->reset(x);")

(defn lazy-seq! [f] "return obj<lazy_sequence>(f);")

(defn list [& s] "return s;")

(defn list? [x] "return x.is_type(type_id<sequence>) ? cached::true_o : cached::false_o;")

(defn seqable? [x] "return runtime::is_seqable(x) ? cached::true_o : cached::false_o;")

(defn cons [x s] "return runtime::cons(x, s);")

(defn first [s] "return runtime::first(s);")
(defn rest [s] "return runtime::rest(s);")

(defn second [s] (first (rest s)))

(defn nth [s ^number_t n] "return runtime::nth(s, n);")
(defn nthrest [s ^number_t n] "return runtime::nthrest(s, n);")

(defn reduce [f r s]
   "var q = r;

    for_each(i, s)
      q = run(f, q, i);

    return q;")

(defn apply [f & s] "return runtime::apply(f, s);")

(defn conj [coll & s] (reduce (fn [h v] (cons v h)) (if (nil? coll) (list) coll) s))

(defn reverse [s] (reduce (fn [h v] (cons v h)) (list) s))

(defn true? [x] "return (x) ? cached::true_o : cached::false_o;")
(defn false? [x] "return (!x) ? cached::true_o : cached::false_o;")

(defn nil? [x] "return x.is_nil() ? cached::true_o : cached::false_o;")

(defn not [x] "return (x) ? cached::false_o : cached::true_o;")

(defn = [& args]
  "var a = runtime::first(args);

   for_each(i, runtime::rest(args)) {
     if (a != i)
       return cached::false_o;
     a = i;
   }

   return cached::true_o;")

(defn identical? [x y] "return (x.get() == y.get()) ? cached::true_o : cached::false_o;")

(defn < [& args]
  "var a = runtime::first(args);

   for_each(b, runtime::rest(args)) {
     if (number::to<real_t>(a) >= number::to<real_t>(b))
       return cached::false_o;
     a = b;
   }

   return cached::true_o;")

(defn > [& args]
  "var a = runtime::first(args);

   for_each(b, runtime::rest(args)) {
     if (number::to<real_t>(a) <= number::to<real_t>(b))
       return cached::false_o;
     a = b;
   }

   return cached::true_o;")

(defn >= [& args]
  "var a = runtime::first(args);

   for_each(b, runtime::rest(args)) {
     if (number::to<real_t>(a) < number::to<real_t>(b))
       return cached::false_o;
     a = b;
   }

   return cached::true_o;")

(defn <= [& args]
  "var a = runtime::first(args);

   for_each(b, runtime::rest(args)) {
     if (number::to<real_t>(a) > number::to<real_t>(b))
       return cached::false_o;
     a = b;
   }

   return cached::true_o;")

(defn count [s] "return obj<number>(runtime::count(s))")

(defn zero? [x] (= x 0))
(defn pos? [x] (> x 0))
(defn neg? [x] (< x 0))

(defn + [& args]
  "real_t value(0.0);

   for_each(i, args)
     value = value + number::to<real_t>(i);

   return obj<number>(value);")

(defn - [& args]
  "var a = runtime::first(args);

   real_t value = number::to<real_t>(a);
   size_t count = 1;

   for_each(i, runtime::rest(args)) {
     value = (value - number::to<real_t>(i));
     count++;
   }

   if (count == 1)
     value = value * real_t(-1.0);

   return obj<number>(value);")

(defn * [& args]
  "real_t value(1.0);

   for_each(i, args)
     value = (value * number::to<real_t>(i));

   return obj<number>(value);")

(defn / [& args]
  "var a = runtime::first(args);

   real_t value = number::to<real_t>(a);
   size_t count = 1;

   for_each(i, runtime::rest(args)) {
     value = (value / number::to<real_t>(i));
     count++;
   }

   if (count == 1)
     value = real_t(1.0) / value;

   return obj<number>(value);")

(defn inc [x] (+ x 1))
(defn dec [x] (- x 1))

(defn min [& args]
  "var m = runtime::first(args);

   for_each(i, runtime::rest(args))
     if (number::to<real_t>(m) > number::to<real_t>(i))
       m = i;

   return m;")

(defn max [& args]
  "var m = runtime::first(args);

   for_each(i, runtime::rest(args))
     if (number::to<real_t>(m) < number::to<real_t>(i))
       m = i;

   return m;")

(defn rem [^number_t num ^number_t div] "return obj<number>((num % div));")

(defn bit-and [^number_t x ^number_t y] "return obj<number>((x & y));")
(defn bit-not [^number_t x] "return obj<number>(~x);")
(defn bit-or [^number_t x ^number_t y] "return obj<number>((x | y));")
(defn bit-xor [^number_t x ^number_t y] "return obj<number>((x ^ y));")

(defn bit-shift-left [^number_t x ^number_t n] "return obj<number>((x << n));")
(defn bit-shift-right [^number_t x ^number_t n] "return obj<number>((x >> n));")

(defn identity [x] x)

(defn map [f coll]
  (lazy-seq!
    (fn []
      (if (seqable? coll)
        (cons (f (first coll)) (map f (rest coll)))))))

(defn range [^number_t n] "return runtime::range(0, n)")

(defn take [n coll]
  (lazy-seq!
    (fn []
      (if (seqable? coll)
        (if (> n 0)
          (cons (first coll) (take (- n 1) (rest coll))))))))

(defn take-while [pred s]
  (lazy-seq!
    (fn []
      (if (seqable? s)
        (if (pred (first s))
          (cons (first s) (take-while pred (rest s))))))))

(defn drop [^number_t n coll] "return runtime::nthrest(coll, n);")

(defn drop-while-aux [pred coll]
  "var s = coll;

   while (run(pred, s))
     s = runtime::rest(s);

   return s;")

(defn drop-while [pred coll]
  (lazy-seq!
    (fn []
      (drop-while-aux (fn [s] (if (seqable? s) (pred (first s)) false)) coll))))

(defn concat1 [x]
  (if (seqable? x)
    (cons (first x) (lazy-seq! (fn [] (concat1 (rest x)))))))

(defn concat [x y]
  (if (seqable? x)
    (cons (first x) (lazy-seq! (fn [] (concat (rest x) y))))
    (concat1 y)))

(defn filter [pred coll]
  (lazy-seq!
    (fn []
      (if (seqable? coll)
        (let [[f & r] coll]
          (if (pred f)
            (cons f (filter pred r))
            (filter pred r)))))))

(defn partition [n coll]
  (lazy-seq!
    (fn []
      (if (seqable? coll)
        (let [p (take n coll)]
          (if (= n (count p))
            (cons p (partition n (nthrest coll n)))))))))

(defn every? [pred coll]
  "for_each(i, coll) {
     if (!run(pred, i))
       return cached::false_o;
   }
   return cached::true_o;")

(defn interleave [s1 s2]
  (lazy-seq!
    (fn []
      (if (seqable? s1)
        (if (seqable? s2)
          (cons (first s1) (cons (first s2) (interleave (rest s1) (rest s2)))))))))

(defn flatten [s]
  (lazy-seq!
    (fn []
      (if (seqable? s)
        (if (seqable? (first s))
          (concat (flatten (first s)) (flatten (rest s)))
          (cons (first s) (flatten (rest s))))))))

(defn string? [s] "return s.is_type(type_id<string>) ? cached::true_o : cached::false_o;")
