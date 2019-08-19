(native-header "fcntl.h"
               "unistd.h"
               "arpa/inet.h"
               "netdb.h"
               "netinet/in.h"
               "sys/poll.h"
               "sys/socket.h"
               "sys/types.h"
               "string.h")

(defobject multicast-socket "io/net/multicast_o.h")

(defn socket [ip port]
  "return obj<multicast_socket>(ip,port);")

(defn pending? [con]
  "if (con.cast<multicast_socket>()->have_pending_data())
     return cached::true_o;
   return cached::false_o;")

(defn send [con data]
  "datagram_t buffer(max_data_gram_size);
   size_t idx = 0; 

   for_each(b, data)
    buffer[idx++] = (byte)number::to<number_t>(b);

   if (con.cast<multicast_socket>()->send(buffer,idx))
      return cached::true_o;
    return cached::false_o;")

(defn byte [data ^size_t curr]
  "datagram_t& buffer = value<datagram_t>::to_reference(data);
   return obj<number>(buffer[curr]);")

(defn data-seq
  ([[size data]]
   (data-seq size data 0))
  ([size data curr]
   (if (< curr size)
     (cons (byte data curr)
           (lazy-seq (data-seq size data (inc curr)))))))

(defn read [conn]
  "return conn.cast<multicast_socket>()->recv();")

(defn recv [conn]
  (data-seq (read conn)))
