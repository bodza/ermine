(defnative open-dir [^c_str directory]
  (on "defined FERRET_STD_LIB"
      ("dirent.h"
       "string.h")
      "DIR *d;
       struct dirent *dir;
       d = opendir(directory);
       if (d) {
         __result = rt::list();
         while ((dir = readdir(d)) != NULL) {
           if (!strcmp(dir->d_name, \".\") || !strcmp(dir->d_name, \"..\")){
             continue;
           }
           __result = rt::cons(obj<string>(dir->d_name), __result);
         }
         closedir(d);
        }
       return __result;"))

(defnative mkdir [^c_str dir]
  (on "defined FERRET_STD_LIB"
      ("sys/stat.h"
       "sys/types.h")
      "int result = mkdir(dir, 0755);
       if (result == 0)
         return cached::true_o;
       return cached::false_o;"))

(defnative rmdir [^c_str dir]
  (on "defined FERRET_STD_LIB"
      ("unistd.h")
      "int result = rmdir(dir);
       if (result == 0)
         return cached::true_o;
       return cached::false_o;"))

(defnative exists [^c_str file]
  (on "defined FERRET_STD_LIB"
      ("unistd.h")
      "if (access( file, F_OK ) != -1)
        return cached::true_o;
       return cached::false_o;"))

(defnative remove [^c_str file]
  (on "defined FERRET_STD_LIB"
      "int result = remove(file);
       if (result == 0)
         return cached::true_o;
       return cached::false_o;"))

(defn seq-flat [s]
  (lazy-seq
   (if (seqable? s)
     (let [[head & tail] s]
       (if (not (string? head))
         (concat (seq-flat head) (seq-flat tail))
         (cons head (seq-flat tail)))))))

(defn seq-walk [dir]
  (map (fn [f]
         (let [file (new-string dir "/" f)]
           (if (open-dir file)
             (new-lazy-seq file #(seq-walk file))
             file)))
       (open-dir dir)))

(defn seq [dir]
  (seq-flat
   (seq-walk dir)))
