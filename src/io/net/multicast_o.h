const size_t max_data_gram_size = 65507;
typedef ferret::array<ferret::byte> datagram_t;

namespace multicast_aux {
  class address{
    sockaddr addr;
    socklen_t addr_len;

  public:
    address(){
      memset(&addr, 0, sizeof(addr));
      addr_len = 0;
    }

    address(const char *hostname, unsigned short port){
      set_host(hostname, port);
    }

    address(const address &src){ copy(src); }

    ~address() { reset(); }

    bool set_host(const char *hostname, unsigned short port);
    void set_any(unsigned short port = 0);

    bool operator==(const address &a) const{
      return addr_len == a.addr_len && memcmp(&addr, &a.addr, addr_len) == 0;
    }

    void copy(const address &src){
      memcpy(&addr, &src.addr, src.addr_len);
      addr_len = src.addr_len;
    }

    void reset(){
      memset(&addr, 0, sizeof(addr));
      addr_len = 0;
    }

    void clear(){
      reset();
    }

    in_addr_t get_in_addr() const;

    friend class udp;
  };

  class udp{
    int fd;

  public:
    unsigned sent_packets;
    size_t sent_bytes;
    unsigned recv_packets;
    size_t recv_bytes;

  public:
    udp() : fd(-1) { close(); }
    ~udp(){ close(); }

    bool open(const char *server_host, unsigned short port, bool blocking);
    bool add_multicast(const address &multiaddr, const address &interface);
    void close();
    bool is_open() const{ return fd >= 0; }

    bool send(const void *data, size_t length, const address &dest);
    ssize_t recv(address &src, datagram_t & recv_buf);

    bool wait(int timeout_ms = -1) const;
    bool have_pending_data() const;
  };

  bool address::set_host(const char *hostname, unsigned short port){
    addrinfo *res = nullptr;
    getaddrinfo(hostname, nullptr, nullptr, &res);
    if (res == nullptr) {
      return false;
    }

    memset(&addr, 0, sizeof(addr));
    addr_len = res->ai_addrlen;
    memcpy(&addr, res->ai_addr, addr_len);
    freeaddrinfo(res);

    // set port for internet sockets
    sockaddr_in *sockname = reinterpret_cast<sockaddr_in *>(&addr);
    if (sockname->sin_family == AF_INET) {
      sockname->sin_port = htons(port);
    }
    else {
      // TODO: any way to set port in general?
    }

    return true;
  }

  void address::set_any(unsigned short port){
    memset(&addr, 0, sizeof(addr));
    sockaddr_in *s = reinterpret_cast<sockaddr_in *>(&addr);
    s->sin_addr.s_addr = htonl(INADDR_ANY);
    s->sin_port = htons(port);
    addr_len = sizeof(sockaddr_in);
  }

  in_addr_t address::get_in_addr() const{
    const sockaddr_in *s = reinterpret_cast<const sockaddr_in *>(&addr);
    return s->sin_addr.s_addr;
  }

  bool udp::open(const char *server_host, unsigned short port, bool blocking){
    // open the socket
    if (fd >= 0) {
      ::close(fd);
    }
    fd = socket(PF_INET, SOCK_DGRAM, 0);

    // set socket as non-blocking
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags < 0) {
      flags = 0;
    }
    fcntl(fd, F_SETFL, flags | (blocking ? 0 : O_NONBLOCK));

    int reuse = 1;
    if (setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, reinterpret_cast<const char *>(&reuse), sizeof(reuse)) != 0) {
      fprintf(stderr, "ERROR WHEN SETTING SO_REUSEADDR ON udp SOCKET\n");
      fflush(stderr);
    }

    int yes = 1;
    // allow packets to be received on this host
    if (setsockopt(fd, IPPROTO_IP, IP_MULTICAST_LOOP, reinterpret_cast<const char *>(&yes), sizeof(yes)) != 0) {
      fprintf(stderr, "ERROR WHEN SETTING IP_MULTICAST_LOOP ON udp SOCKET\n");
      fflush(stderr);
    }

    // bind socket to port if nonzero
    if (port != 0) {
      sockaddr_in sockname;
      sockname.sin_family = AF_INET;
      sockname.sin_addr.s_addr = htonl(INADDR_ANY);
      sockname.sin_port = htons(port);
      bind(fd, reinterpret_cast<struct sockaddr *>(&sockname), sizeof(sockname));
    }

    // add udp multicast groups
    address multiaddr, interface;
    multiaddr.set_host(server_host, port);
    interface.set_any();

    return add_multicast(multiaddr, interface);
  }

  bool udp::add_multicast(const address &multiaddr, const address &interface){
    struct ip_mreq imreq;
    imreq.imr_multiaddr.s_addr = multiaddr.get_in_addr();
    imreq.imr_interface.s_addr = interface.get_in_addr();

    int ret = setsockopt(fd, IPPROTO_IP, IP_ADD_MEMBERSHIP, &imreq, sizeof(imreq));

    return ret == 0;
  }

  void udp::close(){
    if (fd >= 0) {
      ::close(fd);
    }
    fd = -1;

    sent_packets = 0;
    sent_bytes = 0;
    recv_packets = 0;
    recv_bytes = 0;
  }

  bool udp::send(const void *data, size_t length, const address &dest){
    ssize_t len = sendto(fd, data, length, 0, &dest.addr, dest.addr_len);

    if (len > 0) {
      sent_packets++;
      sent_bytes += (size_t)len;
    }

    return (len >= 0 && (size_t)len == length);
  }

  ssize_t udp::recv(address &src, datagram_t & recv_buf){
    src.addr_len = sizeof(src.addr);
    ssize_t len = recvfrom(fd, recv_buf.data, max_data_gram_size, 0, &src.addr, &src.addr_len);

    if (len > 0) {
      recv_packets++;
      recv_bytes += (size_t)len;
    }

    return len;
  }

  bool udp::have_pending_data() const{
    return wait(0);
  }

  bool udp::wait(int timeout_ms) const{
    static const bool debug = false;
    static bool pendingData = false;
    pollfd pfd;
    pfd.fd = fd;
    pfd.events = POLLIN;
    pfd.revents = 0;

    bool success = (poll(&pfd, 1, timeout_ms) > 0);

    if (!success) {
      // Poll now claims that there is no pending data.
      // What did have_pending_data get from Poll most recently?
      if (debug) {
        printf("wait failed, have_pending_data=%s\n", (pendingData ? "true" : "false"));
      }
    }
    pendingData = success;
    return success;
  }
}

class multicast_socket final : public object {
  std::string ip;
  unsigned short port;
  multicast_aux::udp net;
  mutex lock;

public:

  type_t type() const final { return type_id<multicast_socket>; }

#if !defined(FERRET_DISABLE_STD_OUT)
  void stream_console() const final {
    rt::print("multicast_socket<");
    rt::print(ip);
    rt::print(' ');
    rt::print(port);
    rt::print('>');
  }
#endif

  explicit multicast_socket(ref i, ref p) :
    ip(string::to<std::string>(i)),
    port((unsigned short)number::to<number_t>(p)) {
    net.open(ip.c_str(), port,true);
  }

  bool have_pending_data() const {
    return net.have_pending_data();
  }

  bool send(datagram_t & data, size_t size) {
    lock_guard guard(lock);
    multicast_aux::address dest_addr(ip.c_str(), port);
    return net.send(data.data, size, dest_addr);
  }

  var recv(){
    lock_guard guard(lock);
    multicast_aux::address src_addr(ip.c_str(), port);

    var buffer = obj<value<datagram_t>>(max_data_gram_size);
    number_t read = (number_t)net.recv(src_addr, value<datagram_t>::to_reference(buffer));

    return rt::list(obj<number>(read), buffer);
  }
};
