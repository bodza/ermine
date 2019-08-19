(defmacro -> [x & forms]
  (loop [x x, forms forms]
    (if forms
      (let [form (first forms)
            threaded (if (seq? form)
                       `(~(first form) ~x ~@(next form))
                       (list form x))]
        (recur threaded (next forms)))
      x)))
(defmacro ->> [x & forms]
  (loop [x x, forms forms]
    (if forms
      (let [form (first forms)
            threaded (if (seq? form)
                       `(~(first form) ~@(next form)  ~x)
                       (list form x))]
        (recur threaded (next forms)))
      x)))
(defmacro defn [name & body]
  `(def ~name (fn ~@body)))
(defmacro fn [& sig]
  (let [name (if (symbol? (first sig)) (first sig) nil)
        body (if name (rest sig) sig)]
    (if (vector? (first body))
      (let [[args & body] body]
        (new-fir-fn :name name :args args :body body))
      ;; handle multi arity function
      (let [fns   (map (fn* [body]
                            (let [[args & body] body]
                              (new-fir-fn :args args :body body)))
                       body)
            arity (->> (map first body)
                       (map (fn* [args] (filter #(not (= % '&)) args)))
                       (map #(count %)))
            fns   (->> (interleave arity fns)
                       (partition 2)
                       (sort-by first))
            fns   (if (->> fns last second second      ;; last arity arguments
                           (take-last 2) first (= '&)) ;; check &
                    (let [switch        (drop-last 1 fns)
                          [[_ default]] (take-last 1 fns)]
                      `(fir-defn-arity ~switch ~default))
                    `(fir-defn-arity ~fns))]
        (new-fir-fn :escape false :name name :body [fns])))))
(defmacro cxx [& body]
  (let [body (apply str body)]
    `((fn [] ~body))))
(defmacro defnative [name args & form]
  (let [includes (->> (filter #(seq? (nth % 2)) form)
                      (map #(cons (nth % 1) (apply list (nth % 2))))
                      (map (fn [form]
                             (let [[guard & headers] form]
                               (str "\n#if " guard " \n"
                                    (apply str (map #(str "#include \"" % "\"\n") headers))
                                    "#endif\n"))))
                      (map #(list 'native-declare %)))
        enabled (-> (symbol-conversion name)
                    (str "_enabled")
                    .toUpperCase)
        body (->> (map #(vector (second %) (last %)) form)
                  (map #(str "\n#if " (first %) " \n"
                             "#define " enabled "\n"
                             (second %)
                             "\n#endif\n"))
                  (apply str))
        body (str body
                  "\n#if !defined " enabled " \n"
                  "# error " (symbol-conversion name)
                  " Not Supported on This Platform \n"
                  "#endif\n")
        pre-ample (->> (map #(vector (second %) (drop-last (drop 3 %))) form)
                       (remove #(empty? (second %)))
                       (map #(str "\n#if " (first %) " \n"
                                  (apply str (map (fn [line] (str line "\n")) (second %)))
                                  "\n#endif\n"))
                       (map #(list 'native-declare %)))]
    `(def ~name (fn ~args ~@includes ~@pre-ample  ~body))))
(defobject seekable_i "seekable_i.h")
(defobject lambda_i "lambda_i.h")
(defobject deref_i "deref_i.h")
(defn deref [a]
  "return a.cast<deref_i>()->deref();")
(defobject boolean "boolean_o.h")
(defobject pointer "pointer_o.h")
(defobject value "value_o.h")
(defobject number "number_o.h")
(defobject empty_sequence "empty_sequence_o.h")
(defobject sequence "sequence_o.h")
(defobject lazy_sequence "lazy_sequence_o.h")
(defobject array_sequence "array_sequence_o.h")
(defobject d-list "d_list_o.h")

(defn new-d-list-aux [keys vals]
  "return obj<d_list>(keys, vals);")

(defmacro new-d-list [& args]
  (let [kvs (partition 2 args)
        keys (map first kvs)
        vals (map second kvs)]
    `(new-d-list-aux
      (list ~@keys) (list ~@vals))))

(defn assoc [m k v]
  "return m.cast<map_t>()->assoc(k,v);")

(defn dissoc [m k]
  "return m.cast<map_t>()->dissoc(k);")

(defn get [m & args]
  "return m.cast<map_t>()->val_at(args);")

(defn vals [m]
  "return m.cast<map_t>()->vals();")

(defn keys [m]
  "return m.cast<map_t>()->keys();")
(defobject keyword "keyword_o.h")
(defobject string "string_o.h")
(defn new-string
  ([]
   "")
  ([x]
   "return obj<string>(x);")
  ([x y]
   (new-string (concat x y)))
  ([x y & more]
   (new-string (concat x y) (apply concat more))))
(defobject atomic "atomic_o.h")
(defn atom [x]
  "return obj<atomic>(x)")

(defn swap! [a f & args]
  "return a.cast<atomic>()->swap(f,args);")

(defn reset! [a newval]
  "return a.cast<atomic>()->reset(newval);")
(defobject async "async_o.h")

(defmacro future [& body]
  `(_future_ (fn [] ~@body)))

(defn _future_ [f] "return obj<async>(f);")

(defn future-done? [f]
  "if (f.cast<async>()->is_ready())
     return cached::true_o;
   else
     return cached::false_o;")
(defobject delayed "delayed_o.h")

(defn _delay_ [f]
  "return obj<delayed>(f)")

(defmacro delay [& body]
  `(_delay_ (fn [] ~@body)))

(defn delay? [d]
  "if (d.is_type(type_id<delayed>))
     return cached::true_o;
   else
     return cached::false_o;")

(defn force [d] @d)
(defn new-lazy-seq
  ([thunk]
   "return obj<lazy_sequence>(thunk);")
  ([data thunk]
   "return obj<lazy_sequence>(data, thunk);"))

(defmacro lazy-seq [& body]
  `(new-lazy-seq (fn [] ~@body)))

(defn lazy-seq-cache [seq]
  "return lazy_sequence::from(seq);")
(defn list [& xs] "return xs;")
(defn list? [x]
  "if (x.is_type(type_id<sequence>))
     return cached::true_o;
   return cached::false_o;")
(defn seqable? [coll]
  "if (rt::is_seqable(coll))
     return cached::true_o;
   return cached::false_o;")
(defn cons [x seq] "return rt::cons(x, seq);")
(defn first [x]
  "return rt::first(x);")
(defn second [x]
  "return rt::first(rt::rest(x));")
(defn rest [x] "return rt::rest(x);")
(defn nth [coll ^number_t index]
  "return rt::nth(coll,index);")
(defn nthrest [coll ^number_t n]
  "return rt::nthrest(coll,n);")
(defn reduce
  ([f xs]
   (reduce f (first xs) (rest xs)))
  ([f acc coll]
   "__result = acc;
    for_each(i, coll)
     __result = run(f, __result, i);"))
(defn apply [f & argv]
  "return rt::apply(f,argv);")
(defn conj [coll & xs]
  (reduce (fn[h v] (cons v h)) (if (nil? coll) (list) coll) xs))
(defn reverse [s]
  (reduce (fn[h v] (cons v h)) (list) s))
(defn true? [x]
  "if (x)
     return cached::true_o;
   return cached::false_o;")
(defn false? [x]
  "if (!x)
     return cached::true_o;
   return cached::false_o;")
(defn nil? [x]
  "if (x.is_nil())
       return cached::true_o;
   return cached::false_o;")
(defn not [x]
  "if (x)
     return cached::false_o;
   return cached::true_o;")
(defn = [& args]
  "var curr = rt::first(args);
   for_each(it, rt::rest(args)){
    if (curr != it)
      return cached::false_o;
    curr = it;
   }
   return cached::true_o;")
(defmacro not= [& test]
  `(not (= ~@test)))
(defn identical? [x y]
  "if(x.get() == y.get())
    return cached::true_o;
   return cached::false_o;")
(defn < [& args]
  "var a = rt::first(args);

   for_each(b, rt::rest(args)){
    if (number::to<real_t>(a) >= number::to<real_t>(b))
      return cached::false_o;
    a = b;
   }

   return cached::true_o;")
(defn > [& args]
  "var a = rt::first(args);

   for_each(b, rt::rest(args)){
    if (number::to<real_t>(a) <= number::to<real_t>(b))
      return cached::false_o;
    a = b;
   }

   return cached::true_o;")
(defn >= [& args]
  "var a = rt::first(args);

   for_each(b, rt::rest(args)){
    if (number::to<real_t>(a) < number::to<real_t>(b))
      return cached::false_o;
    a = b;
   }

   return cached::true_o;")
(defn <= [& args]
  "var a = rt::first(args);

   for_each(b, rt::rest(args)){
    if (number::to<real_t>(a) > number::to<real_t>(b))
      return cached::false_o;
    a = b;
   }

   return cached::true_o;")
(defmacro and
  ([] true)
  ([x] x)
  ([x & next]
   `(if ~x (and ~@next) false)))
(defmacro or
  ([] nil)
  ([x] x)
  ([x & next]
   `(if ~x ~x (or ~@next))))
(defmacro when [test & body]
  `(if ~test (do ~@body)))
(defmacro cond [& clauses]
  (when clauses
    `(if ~(first clauses)
       ~(if (next clauses)
          (second clauses)
          (throw (IllegalArgumentException.
                  "cond requires an even number of forms")))
       (cond ~@(next (next clauses))))))
(defn _while_ [pred fn]
  "while(run(pred))
     run(fn);")

(defmacro while [test & body]
  `(_while_ (fn [] ~test) (fn [] ~@body)))
(defn _while-let_ [pred fn]
  "var v;
   while((v = run(pred)))
     run(fn,v);")

(defmacro while-let
  [[form test] & body]
  `(_while-let_ (fn [] ~test) (fn [~form] ~@body)))
(defmacro forever [& body]
  `(while true ~@body))
(defmacro if-let
  ([bindings then]
   `(if-let ~bindings ~then nil))
  ([bindings then else & oldform]
   (let [form (bindings 0) tst (bindings 1)]
     `(let* [temp# ~tst]
        (if temp#
          (let* [~form temp#]
            ~then)
          ~else)))))
(defmacro when-let
  [bindings & body]
  (let [form (bindings 0) tst (bindings 1)]
    `(let* [temp# ~tst]
       (when temp#
         (let* [~form temp#]
           ~@body)))))
(defn count [s] "return obj<number>(rt::count(s))")
(defn zero? [x]
  (= x 0))
(defn pos? [x]
  (> x 0))
(defn neg? [x]
  (< x 0))
(defn + [& args]
  "real_t value(0.0);

   for_each(i, args)
    value = value + number::to<real_t>(i);

   __result = obj<number>(value);")
(defn - [& args]
  "__result = rt::first(args);
   real_t value = number::to<real_t>(__result);
   size_t count = 1;

   for_each(i, rt::rest(args)){
    value = (value - number::to<real_t>(i));
    count++;
   }

   if (count == 1)
    value = value * real_t(-1.0);

   __result = obj<number>(value);")
(defn * [& args]
  "real_t value(1.0);

   for_each(i, args)
    value = (value * number::to<real_t>(i));

   __result = obj<number>(value);")
(defn / [& args]
  "__result = rt::first(args);
   real_t value = number::to<real_t>(__result);
   size_t count = 1;

   for_each(i, rt::rest(args)){
    value = (value / number::to<real_t>(i));
    count++;
   }

   if (count == 1)
    value = real_t(1.0) / value;

   __result = obj<number>(value);")
(defn inc [x]
  (+ x 1))
(defn dec [x]
  (- x 1))
(defn min [& args]
  "__result = rt::first(args);
   for_each(i, rt::rest(args))
    if (number::to<real_t>(__result) > number::to<real_t>(i))
     __result = i;")
(defn max [& args]
  "__result = rt::first(args);
   for_each(i, rt::rest(args))
    if (number::to<real_t>(__result) < number::to<real_t>(i))
     __result = i;")
(defn rem [^number_t num ^number_t div]
  "return obj<number>((num % div));")
(defn mod [num div] 
  (let [m (rem num div)] 
    (if (or (zero? m) (= (pos? num) (pos? div)))
      m 
      (+ m div))))
(defn floor [^number_t x] "return obj<number>(x);")
(defn interp [^real_t x
              ^real_t in-min ^real_t in-max
              ^real_t out-min ^real_t out-max]
  "return obj<number>((x - in_min) * (out_max - out_min) / (in_max - in_min) + out_min);")
(defn clip [^number_t x ^number_t min ^number_t max]
  "return obj<number>(rt::max(rt::min(max, x), min));")
(defn bit-and [^number_t x ^number_t y] "return obj<number>((x & y));")
(defn bit-not [^number_t x] "return obj<number>(~x);")
(defn bit-or [^number_t x ^number_t y] "return obj<number>((x | y ));")
(defn bit-xor [^number_t x ^number_t y] "return obj<number>((x ^ y ));")
(defn bit-shift-left [^number_t x ^number_t n] "return obj<number>((x << n ));")
(defn bit-shift-right [^number_t x ^number_t n] "return obj<number>((x >> n ));")
(defn bit-extract [^number_t x ^number_t p ^number_t k]
  "__result = obj<number>((x >> p) & ((1 << k) - 1));")
(defn bit-override [^number_t dst ^number_t src ^number_t pos ^number_t len]
  "number_t mask = (((number_t)1 << len) - 1) << pos;
   number_t num = (dst & ~mask) | (src & mask);
   return obj<number>(num);")
(defn encode-int16 [n] 
  "int16_t val = number::to<int16_t>(n);
   byte *p = (byte*)&val;
   for (int i = (sizeof(int16_t) -1); i >= 0; i--)
     __result = rt::cons(obj<number>((number_t)p[i]),__result);")
(defn decode-int16 [s]
  "int16_t val = 0;
   byte *p = (byte*)&val; 

   size_t index = 0;
   for_each(i, s){
     p[index] = number::to<byte>(i);
     index++;
   }

   return obj<number>(val);")
(defn encode-float [n] 
  "static_assert(sizeof(float) == 4 * sizeof(byte), \"\");
   float val = number::to<float>(n);
   byte *p = (byte*)&val;
   for (int i = (sizeof(float) -1); i >= 0; i--)
     __result = rt::cons(obj<number>(p[i]),__result);")
(defn decode-float [s]
  "union {
    float f;
    byte b[4];
   } u;
   static_assert(sizeof(float) == 4 * sizeof(byte), \"\");

   size_t index = 0;
   for_each(i, s){
     if (index > 3)
      break;
     u.b[index] = number::to<byte>(i);
     index++;
   }

   return obj<number>(u.f);")
(defn sqrt [^real_t s]
  "return obj<number>(::sqrt(s));")
(defn pow [^real_t b ^real_t e]
  "return obj<number>(::pow(b, e));")
(defn cos [^real_t s]
  "return obj<number>(::cos(s));")
(defn sin [^real_t s]
  "return obj<number>(::sin(s));")
(defn asin [^real_t x]
  "return obj<number>(::asin(x));")
(defn atan2 [^real_t x ^real_t y]
  "return obj<number>(::atan2(x,y));")
(defn log [^real_t x]
  "return obj<number>(::log(x));")
(defn log10 [^real_t x]
  "return obj<number>(::log10(x));")
(defn to-degrees [^real_t x]
  "return obj<number>((x * 180.0 / 1_pi));")
(defn to-radians [^real_t x]
  "return obj<number>((x * 1_pi / 180.0));")
(defn identity [x] x)
(defn thread [f]
  "return obj<async>(f);")
(defnative get-char []
  (on "defined ERMINE_STD_LIB"
      "return obj<number>(getchar());"))
(defnative sleep [^number_t t]
  (on "defined ERMINE_STD_LIB"
      "auto duration = ::std::chrono::milliseconds(t);
       ::std::this_thread::sleep_for(duration);")
  (on "defined ERMINE_HARDWARE_ARDUINO"
      "::delay(t);"))
(defmacro doseq [binding & body]
  `(_doseq_ ~(second binding)
            (fn [~(first binding)] ~@body)))

(defn _doseq_ [seq f] "for_each(it, seq) run(f,it);")
(defmacro dotimes [binding & body]
  `(_dotimes_ ~(second binding)
              (fn [~(first binding)] ~@body)))

(defn _dotimes_ [^number_t t f] "for(number_t i = 0; i < t; i++) run(f,obj<number>(i));")
(defn map [f coll]
  (lazy-seq
   (if (seqable? coll)
     (cons (f (first coll))
           (map f (rest coll))))))
(defn range
  ([high]
   (range 0 high))
  ([^number_t low ^number_t high]
   "return rt::range(low, high)"))
(defn take [n coll]
  (lazy-seq
   (if (seqable? coll)
     (if (> n 0)
       (cons (first coll)
             (take (- n 1) (rest coll)))))))
(defn take-while [pred s]
  (lazy-seq
   (if (and (seqable? s)
            (pred (first s)))
     (cons (first s) (take-while pred (rest s))))))
(defn drop [^number_t n coll]
  "return rt::nthrest(coll, n);")
(defn drop-while-aux [p c]
  "__result = c;
   while(run(p,__result))
     __result = rt::rest(__result);")

(defn drop-while [pred coll]
  (lazy-seq
   (drop-while-aux #(and (seqable? %) (pred (first %))) coll)))
(defn concat
  ([]
   (list))
  ([x]
   (if (seqable? x)
     (cons (first x) (lazy-seq (concat (rest x))))))
  ([x y]
   (if (seqable? x)
     (cons (first x) (lazy-seq (concat (rest x) y)))
     (concat y)))
  ([x y & more]
   (concat (concat x y) (apply concat more))))
(defn filter [pred coll]
  (lazy-seq
   (if (seqable? coll)
     (let [[f & r] coll]
       (if (pred f)
         (cons f (filter pred r))
         (filter pred r))))))
(defn repeatedly
  ([f]   (lazy-seq (cons (f) (repeatedly f))))
  ([n f] (take n (repeatedly f))))
(defn partition
  ([n coll]
   (partition n n coll))
  ([n step coll]
   (lazy-seq
    (if (seqable? coll)
      (let [p (take n coll)]
        (when (= n (count p))
          (cons p (partition n step (nthrest coll step))))))))
  ([n step pad coll]
   (lazy-seq
    (if (seqable? coll)
      (let [p (take n coll)]
        (if (= n (count p))
          (cons p (partition n step pad (nthrest coll step)))
          (list (take n (concat p pad)))))))))
(defn every? [pred coll]
  "for_each(i, coll){
     if (!run(pred, i))
      return cached::false_o;
   }
   return cached::true_o;")
(defn interleave
  ([s1 s2]
   (lazy-seq
    (when (and (seqable? s1)
               (seqable? s2))
      (cons (first s1) (cons (first s2)
                             (interleave (rest s1) (rest s2))))))))
(defn flatten [s]
  (lazy-seq
   (if (seqable? s)
     (if (seqable? (first s))
       (concat (flatten (first s)) (flatten (rest s)))
       (cons (first s) (flatten (rest s)))))))
(defnative rand-aux []
  (on "defined ERMINE_STD_LIB"
      ("random")
      "::std::random_device ermine_random_device;
       ::std::mt19937_64 ermine_random_generator(ermine_random_device());
       ::std::uniform_real_distribution<ermine::real_t> ermine_random_distribution(0.0,1.0);"
      "return obj<number>(ermine_random_distribution(ermine_random_generator));"))

(defn rand
  ([]
   (rand-aux))
  ([x]
   (* x (rand-aux))))
(defn rand-int
  [x]
  (floor (rand x)))
(defnative millis []
  (on "defined ERMINE_STD_LIB"
      "auto now = ::std::chrono::system_clock::now();
       auto epoch = now.time_since_epoch();
       auto time = ::std::chrono::duration_cast<::std::chrono::milliseconds>(epoch).count();
       return obj<number>(time);")
  (on "defined ERMINE_HARDWARE_ARDUINO"
      "return obj<number>(::millis());"))
(defnative micros []
  (on "defined ERMINE_STD_LIB"
      "auto now = ::std::chrono::high_resolution_clock::now();
       auto epoch = now.time_since_epoch();
       auto time = ::std::chrono::duration_cast<::std::chrono::microseconds>(epoch).count();
       return obj<number>(time);")
  (on "defined ERMINE_HARDWARE_ARDUINO"
      "return obj<number>(::micros());"))
(defnative sleep-micros [^number_t t]
  (on "defined ERMINE_STD_LIB"
      "auto duration = ::std::chrono::microseconds(t);
       ::std::this_thread::sleep_for(duration);")
  (on "defined ERMINE_HARDWARE_ARDUINO"
      "::delayMicroseconds(t);"))
(defobject elapsed_micros "elapsed_micros_o.h")

(defn new-elapsed-micros []
  "return obj<elapsed_micros>();")

(defn elapsed-micros? [t ^real_t n]
  "if (t.cast<elapsed_micros>()->is_elapsed(n))
     return cached::true_o;
   return cached::false_o;")

(defn elapsed-micros-now [t]
  "return obj<number>(t.cast<elapsed_micros>()->elapsed());")

(defn elapsed-micros-reset [t]
  "t.cast<elapsed_micros>()->reset()")
(defn benchmark
  ([f]
   (benchmark f 100))
  ([f ^number_t n]
   "elapsed_micros timer;

    run(f);
    real_t elapsed = timer.elapsed() / real_t(1000.0);

    real_t min = elapsed;
    real_t max = elapsed;
    real_t sum = real_t(0.0);
    real_t sum_sq = real_t(0.0);

    for(number_t i =0; i < n; i++){
      timer.reset();
      run(f);
      real_t elapsed = timer.elapsed() / real_t(1000.0);

      #if defined(ERMINE_BENCHMARK_VERBOSE)
         rt::println(elapsed);
      #endif

      sum += elapsed;
      sum_sq += (elapsed * elapsed);
      if (elapsed < min)
        min = elapsed;
      if (elapsed > max)
        max = elapsed;
      }

      real_t mean = (real_t)(sum / n);
      real_t stdev = (real_t)sqrt((sum_sq / n) - (mean * mean));

      rt::print(\"\\t mean: \");
      rt::println(mean);

      rt::print(\"\\tstdev: \");
      rt::println(stdev);

      rt::print(\"\\t  min: \");
      rt::println(min);

      rt::print(\"\\t  max: \");
      rt::println(max);

      rt::print(\"\\trange: \");
      rt::println((max - min));"))
(defobject fn_throttler_o "fn_throttler_o.h")

(defn new-fn-throttler [f ^real_t rate ^bolean block]
  "return obj<fn_throttler>(f, rate, block);")

(defmacro fn-throttler [f rate unit policy]
  (let [unit->ms {:microsecond 1 :millisecond 1000
                  :second 1000000 :minute 60000000
                  :hour 3600000000 :day 86400000000
                  :month 2678400000000}
        rate (/ (unit->ms unit) rate)]
    `(new-fn-throttler ~f ~rate ~(= policy :blocking))))
(defn string? [s]
  "if (s.is_type(type_id<string>))
     return cached::true_o;
   return cached::false_o;")
(defn ston [str]
  "var seq = str;
   real_t factor = 1;
   real_t value = 0;

   if (number::to<byte>(rt::first(seq)) == '-'){
     seq = rt::rest(seq);
     factor = -1;
   }

   bool point_passed = false;
   for_each(i, seq){
     byte ch = number::to<byte>(i);

     if (ch == '.'){
       point_passed = true;
       continue;
     }

     number_t d = ch - '0';
     if (d >= 0 && d <= 9){
       if (point_passed)
         factor /= real_t(10.0);
       value = value * real_t(10.0) + real_t(d);
     }
   }

   return obj<number>(value * factor);")
(defn ntos [^real_t f]
  "number_t n = (number_t)f;
   number_t sign;

   if ((sign = n) < 0){
      n = -n;
      f = -f;
   }

   var s;

   f = (f - n) + 10;
   for (int i = real_precision; i >= 1; i--){
      number_t ch = ((number_t)(f * ::pow(10, i)) % 10) + '0';
      s = rt::cons(obj<number>(ch), s);
   }

   s = rt::cons(obj<number>('.'), s);

   do {
     s = rt::cons(obj<number>(n % 10 + '0'), s);
    } while ((n /= 10) > 0);

   if (sign < 0)
     s = rt::cons(obj<number>('-'), s);

   return obj<string>(s);")
(defnative str-tok [str delimeter]
  (on "defined ERMINE_RUNTIME_H"
      ("string.h")
      "var packed_delimeter = string::pack(delimeter);
       var packed_str = string::pack(str);

       class seq : public lambda_i {
         var s;
         var d;
       public:
         explicit seq(ref str = nil(), ref del = nil()) : s(str), d(del) { }
         var invoke(ref) const final {
           char* token = strtok(NULL, string::c_str(d));
           if (token != nullptr)
             return obj<lazy_sequence>(obj<string>(token),obj<seq>(s, d));
           return nil();
         }
       };

       char* token = strtok(string::c_str(packed_str), 
                            string::c_str(packed_delimeter)); 

       if (token != nullptr)
         return obj<lazy_sequence>(obj<string>(token),
                                   obj<seq>(packed_str, packed_delimeter));

       return nil();"))
(defmacro doto
  [x & forms]
  (let [gx (gensym)]
    `(let [~gx ~x]
       ~@(map (fn [f]
                (if (seq? f)
                  `(~(first f) ~gx ~@(next f))
                  `(~f ~gx)))
              forms)
       ~gx)))
(defmacro comment
  [& body])
(defnative print [& more]
  (on "!defined(ERMINE_DISABLE_STD_OUT)"
      "if (more.is_nil())
         return nil();
       ref f = rt::first(more);
       f.stream_console();
       ref r = rt::rest(more);
       for_each(it, r){
        rt::print(' ');
        it.stream_console();
       }
       return nil();"))
(defn println [& more]
  (apply print more)
  (cxx "rt::print((char)0xA);"))
(defn read-line []
  "char buf[ERMINE_IO_STREAM_SIZE] = {0};
   rt::read_line(buf, ERMINE_IO_STREAM_SIZE);
   return obj<string>(buf);")
(defnative slurp [^c_str f]
  (on "defined ERMINE_STD_LIB"
      ("fstream")
      "std::ifstream ifs(f, std::ios::in | std::ios::binary | std::ios::ate);

       if (!ifs.good())
         return nil();

       std::ifstream::pos_type file_size = ifs.tellg();
       ifs.seekg(0, std::ios::beg);

       var data = obj<array_seq<byte, number>>(size_t(file_size));
       var storage = (data.cast<array_seq<byte, number>>()->storage);
       auto& arr = value<array<byte>>::to_reference(storage).data;

       ifs.read((char*)arr, file_size);

       return obj<string>(data);"))
(defnative sh [^c_str cmd]
  (on "defined ERMINE_STD_LIB"
      ("memory")
      "::std::shared_ptr<FILE> pipe(popen(cmd, \"r\"), pclose);
       if (!pipe) 
         return nil();
       char buffer[128];
       ::std::string result = \"\";
       while (!feof(pipe.get()))
        if (fgets(buffer, 128, pipe.get()) != NULL)
         result += buffer;
       return obj<string>(result);"))
(defnative lock-memory []
  (on "defined ERMINE_STD_LIB"
      ("sys/mman.h")
      "mlockall(MCL_CURRENT | MCL_FUTURE);"))
(defn pr-object-sizes []
  (println "Machine Types")
  (println "\t*void:\t\t\t" (cxx "return obj<number>(sizeof(void*));"))
  (println "\treal_t:\t\t\t" (cxx "return obj<number>(sizeof(real_t));"))
  (println "\tnumber_t:\t\t" (cxx "return obj<number>(sizeof(number_t));"))
  (println "Object Types")
  (println "\tvar:\t\t\t" (cxx "return obj<number>(sizeof(var));"))
  (println "\tobject:\t\t\t" (cxx "return obj<number>(sizeof(object));"))
  (println "\tnumber:\t\t\t" (cxx "return obj<number>(sizeof(number));"))
  (println "\tkeyword:\t\t" (cxx "return obj<number>(sizeof(keyword));"))
  (println "\tboolean:\t\t" (cxx "return obj<number>(sizeof(boolean));"))
  (println "\tempty_sequence:\t\t" (cxx "return obj<number>(sizeof(empty_sequence));"))
  (println "\tsequence:\t\t" (cxx "return obj<number>(sizeof(sequence));"))
  (println "\tlazy_sequence:\t\t" (cxx "return obj<number>(sizeof(lazy_sequence));"))
  (println "\tatom:\t\t\t" (cxx "return obj<number>(sizeof(atomic));"))
  (println "\td_list:\t\t\t" (cxx "return obj<number>(sizeof(d_list));"))
  (println "\tpointer:\t\t" (cxx "return obj<number>(sizeof(pointer));"))
  (println "\telapsed_micros:\t\t" (cxx "return obj<number>(sizeof(elapsed_micros));"))
  (println "\tdelayed:\t\t" (cxx "return obj<number>(sizeof(delayed));"))
  (println "\tstring:\t\t\t" (cxx "return obj<number>(sizeof(string));"))
  (println "Interface Types")
  (println "\tseekable_i:\t\t" (cxx "return obj<number>(sizeof(seekable_i));"))
  (println "\tlambda_i:\t\t" (cxx "return obj<number>(sizeof(lambda_i));"))
  (println "\tderef_i:\t\t" (cxx "return obj<number>(sizeof(deref_i));")))
(defnative memory-pool-free-space []
  (on "defined ERMINE_MEMORY_POOL_SIZE"
      "size_t acc = 0;
       for(size_t i = 0; i < ERMINE_MEMORY_POOL_PAGE_COUNT; i++)
         if(memory::allocator::program_memory.used.get(i) == false)
           acc++;
       return obj<number>((acc*sizeof(ERMINE_MEMORY_POOL_PAGE_TYPE)));"))
(defn system-exit []
  "::exit(0);")
(defn system-abort []
  "::abort();")
(defn system-halt [code]
  (forever (sleep 1000)))
(defobject fsm "fsm_o.h")

(defn new-fsm [state transitions]
  "return obj<fsm>(state, transitions)")

(defmacro fsm [& transitions]
  (let [fsm-state (gensym)
        switch    (->> (reduce
                        (fn [h v]
                          (let [[state & conds] v
                                at-state `(= ~state ~fsm-state)
                                jmp (if (= (count conds) 1)
                                      (first conds)
                                      (->> (reduce
                                            (fn [h v]
                                              (let [[check state] v]
                                                (conj h `(~check) state)))
                                            ['cond] (partition 2 conds))
                                           (apply list)))]
                            (conj h at-state jmp)))
                        ['cond] transitions)
                       (apply list))]
    `(new-fsm
      ~(-> transitions first first)
      (fn [~fsm-state] ~switch))))

(defmacro configure-runtime! [& body]
  `(native-define ~(->> (partition 2 body)
                        (map #(str "#define " (first %) " " (second %) "\n"))
                        (list))))
(defmacro configure-ermine! [& body]
  `(native-define ~(str "// build-conf-begin\n"
                        "//" (str (apply hash-map body)) "\n"
                        "// build-conf-end\n")))


(native-header "termios.h"
               "fcntl.h"
               "unistd.h"
               "sys/ioctl.h")

(defn open-aux [^c_str port speed v-min v-time]
  "struct termios toptions;
   int fd;

   fd = open(port, O_RDWR | O_NOCTTY | O_NDELAY);

   if (fd == -1){
     return nil();
    }else{

     if (tcgetattr(fd, &toptions) < 0) {
       return nil();
     }else{

     speed_t rate = B9600;

     switch (number::to<number_t>(speed)) {
         case 9600:
             rate = B9600;
             break;
         case 19200:
             rate = B19200;
             break;
         case 38400:
             rate = B38400;
             break;
         case 57600:
             rate = B57600;
             break;
         case 115200:
             rate = B115200;
             break;
         case 230400:
             rate = B230400;
             break;
         case 460800:
             rate = B460800;
             break;
         case 500000:
             rate = B500000;
             break;
         case 576000:
             rate = B576000;
             break;
         case 921600:
             rate = B921600;
             break;
         case 1000000:
             rate = B1000000;
             break;
         case 1152000:
             rate = B1152000;
             break;
         case 1500000:
             rate = B1500000;
             break;
         case 2000000:
             rate = B2000000;
             break;
         case 2500000:
             rate = B2500000;
             break;
         case 3000000:
             rate = B3000000;
             break;
         case 3500000:
             rate = B3500000;
             break;
         case 4000000:
             rate = B4000000;
             break;
         default: 
             return nil();
      }

      cfsetispeed(&toptions, rate);
      cfsetospeed(&toptions, rate);

      // 8N1
      toptions.c_cflag &= (tcflag_t)~PARENB;
      toptions.c_cflag &= (tcflag_t)~CSTOPB;
      toptions.c_cflag &= (tcflag_t)~CSIZE;
      toptions.c_cflag |= (tcflag_t)CS8;
      // no flow control
      toptions.c_cflag &= (tcflag_t)~CRTSCTS;

      toptions.c_cflag |= (tcflag_t)CREAD | CLOCAL;  // turn on READ & ignore ctrl lines
      toptions.c_iflag &= (tcflag_t)~(IXON | IXOFF | IXANY); // turn off s/w flow ctrl

      toptions.c_lflag &= (tcflag_t)~(ICANON | ECHO | ECHOE | ISIG); // make raw
      toptions.c_oflag &= (tcflag_t)~OPOST; // make raw

      toptions.c_cc[VMIN]  = (cc_t)number::to<number_t>(v_min);
      toptions.c_cc[VTIME] = (cc_t)number::to<number_t>(v_time);

      if( tcsetattr(fd, TCSANOW, &toptions) < 0) {
       return nil();
      }else
        return obj<number>(fd);
    }
   }")

(defn open
  ([port]
   (open-aux port 9600 0 20))
  ([port speed]
   (open-aux port speed 0 20))
  ([port speed v-min v-time]
   (open-aux port speed v-min v-time)))


(defn write [^number_t port ^byte data]
  "byte b[1] = {data};
   write(port, b, 1);")

(defn available [^number_t port]
  "int bytes_ready;
   int op = ioctl(port, FIONREAD, &bytes_ready);
   if (op == -1)
     return nil();
   return obj<number>(bytes_ready);")

(defn read [^number_t port]
  "char b[1] = {0};
   ssize_t bytes_read = read(port, b, 1);

   if (bytes_read == -1)
     return nil();
   else
     return obj<number>(b[0]);")
