// Detect Hardware
# define FERRET_CONFIG_SAFE_MODE TRUE

#if !defined(FERRET_SAFE_MODE)
  #if defined(__APPLE__) ||                       \
    defined(_WIN32) ||                            \
    defined(__linux__) ||                         \
    defined(__unix__) ||                          \
    defined(_POSIX_VERSION)

    # undef  FERRET_CONFIG_SAFE_MODE
    # define FERRET_STD_LIB TRUE
  #endif

  #if defined(ARDUINO)

    # define FERRET_HARDWARE_ARDUINO TRUE

    #if !defined(FERRET_HARDWARE_ARDUINO_UART_PORT)
      # define FERRET_HARDWARE_ARDUINO_UART_PORT Serial
    #endif
  #endif

  #if defined(FERRET_HARDWARE_ARDUINO)
    # undef  FERRET_CONFIG_SAFE_MODE
    # define FERRET_DISABLE_STD_MAIN TRUE
  #endif
#endif

#if defined(FERRET_CONFIG_SAFE_MODE)
  # define FERRET_DISABLE_MULTI_THREADING TRUE
  # define FERRET_DISABLE_STD_OUT TRUE
#endif
#ifdef FERRET_STD_LIB
 #include <iostream>
 #include <iomanip>
 #include <sstream>
 #include <cstdio>
 #include <cstdlib>
 #include <cstddef>
 #include <cmath>
 #include <vector>
 #include <algorithm>
 #include <chrono>
 #include <atomic>
 #include <mutex>
 #include <thread>
 #include <future>
#endif

#ifdef FERRET_HARDWARE_ARDUINO
 #include <Arduino.h>
 #include <stdio.h>
 #include <stdlib.h>
 #include <stdint.h>
#endif

#ifdef FERRET_CONFIG_SAFE_MODE
 #include <stdio.h>
 #include <stdlib.h>
 #include <stdint.h>
 #include <math.h>
#endif

namespace ferret{
  namespace runtime {}
  namespace rt = runtime;
  // Types
  typedef uint8_t byte;
  #pragma pack(push, 1)
  class int24_t {
  protected:
    byte word[3];
  public:
    int24_t(){ }
  
    template<typename T>
    explicit int24_t( T const & val ) {
      *this   = (int32_t)val;
    }
  
    int24_t( const int24_t& val ) {
      *this   = val;
    }
  
    operator int32_t() const {
      if (word[2] & 0x80) { // negative? - then sign extend.
        return
          (int32_t)(((uint32_t)0xff    << 24) |
                    ((uint32_t)word[2] << 16) |
                    ((uint32_t)word[1] << 8)  |
                    ((uint32_t)word[0] << 0));
      }else{
        return
          (int32_t)(((uint32_t)word[2] << 16) |
                    ((uint32_t)word[1] << 8)  |
                    ((uint32_t)word[0] << 0));
      }
    }
  
    int24_t& operator =( const int24_t& input ) {
      word[0]   = input.word[0];
      word[1]   = input.word[1];
      word[2]   = input.word[2];
  
      return *this;
    }
  
    int24_t& operator =( const int32_t input ) {
      word[0]   = ((byte*)&input)[0];
      word[1]   = ((byte*)&input)[1];
      word[2]   = ((byte*)&input)[2];
  
      return *this;
    }
  
    int24_t operator +( const int24_t& val ) const {
      return int24_t( (int32_t)*this + (int32_t)val );
    }
  
    int24_t operator -( const int24_t& val ) const {
      return int24_t( (int32_t)*this - (int32_t)val );
    }
  
    int24_t operator *( const int24_t& val ) const {
      return int24_t( (int32_t)*this * (int32_t)val );
    }
  
    int24_t operator /( const int24_t& val ) const {
      return int24_t( (int32_t)*this / (int32_t)val );
    }
  
    int24_t& operator +=( const int24_t& val ) {
      *this   = *this + val;
      return *this;
    }
  
    int24_t& operator -=( const int24_t& val ) {
      *this   = *this - val;
      return *this;
    }
  
    int24_t& operator *=( const int24_t& val ) {
      *this   = *this * val;
      return *this;
    }
  
    int24_t& operator /=( const int24_t& val ) {
      *this   = *this / val;
      return *this;
    }
  
    int24_t operator -() {
      return int24_t( -(int32_t)*this );
    }
  
    bool operator ==( const int24_t& val ) const {
      return (int32_t)*this == (int32_t)val;
    }
  
    bool operator !=( const int24_t& val ) const {
      return (int32_t)*this != (int32_t)val;
    }
  
    bool operator >=( const int24_t& val ) const {
      return (int32_t)*this >= (int32_t)val;
    }
  
    bool operator <=( const int24_t& val ) const {
      return (int32_t)*this <= (int32_t)val;
    }
  
    bool operator >( const int24_t& val ) const {
      return (int32_t)*this > (int32_t)val;
    }
  
    bool operator <( const int24_t& val ) const {
      return (int32_t)*this < (int32_t)val;
    }
  };
  #pragma pack(pop)
  // Concurrency
  #if defined(FERRET_DISABLE_MULTI_THREADING)
    class mutex {
    public:
      void lock()   {} 
      void unlock() {} 
    };
  #else
    #if defined(FERRET_STD_LIB)
      class mutex {
        ::std::mutex m;
      public:
        void lock()   { m.lock();   } 
        void unlock() { m.unlock(); }
      };
    #endif
  
    #if defined(FERRET_HARDWARE_ARDUINO)
      class mutex {
      public:
        void lock()   { noInterrupts(); } 
        void unlock() { interrupts();   }
      };
    #endif
  #endif
  
  class lock_guard{
    mutex & _ref;
  public:
    explicit lock_guard(const lock_guard &) = delete;
    explicit lock_guard(mutex & mutex) : _ref(mutex) { _ref.lock(); };
    ~lock_guard() { _ref.unlock(); }
  };
  // Containers
  #undef bit
  
  #if !defined(FERRET_BITSET_WORD_TYPE)
    #define FERRET_BITSET_WORD_TYPE unsigned int
    #if defined(__clang__) || defined(__GNUG__)
      #define FERRET_BITSET_USE_COMPILER_INTRINSICS true
    #endif
  #endif
  
  template<size_t S, typename word_t = FERRET_BITSET_WORD_TYPE>
  class bitset {
    static const size_t bits_per_word = sizeof(word_t) * 8;
    static const size_t n_words = S / bits_per_word;
  
    static_assert((S % bits_per_word) == 0, "bitset size must be a multiple of word_t");
  
    word_t bits[n_words];
  
    inline size_t word (size_t i) const { return i / bits_per_word; }
    inline size_t bit  (size_t i) const { return i % bits_per_word; }
  
  public:
    bitset() : bits{ word_t(0x00) } { }
  
    inline void set   (size_t b){
      bits[word(b)] = (word_t)(bits[word(b)] |  (word_t(1) << (bit(b))));
    }
  
    inline void set (size_t b, size_t e){
      size_t word_ptr = word(b);
      size_t n_bits = e - b;
  
      bits[word_ptr] = (word_t)(bits[word_ptr] | bit_block(bit(b), n_bits));
  
      n_bits -= bits_per_word - bit(b);
      word_ptr++;
      size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
      for (; word_ptr < last_word; word_ptr++){
        bits[word_ptr] = (word_t)(bits[word_ptr] | bit_block(0, n_bits));
        n_bits -= bits_per_word;
      }
    }
  
    inline void reset (size_t b){
      bits[word(b)] = (word_t)(bits[word(b)] & ~(word_t(1) << (bit(b))));
    }
  
    inline void reset (size_t b, size_t e){
      size_t word_ptr = word(b);
      size_t n_bits = e - b;
  
      bits[word_ptr] = (word_t)(bits[word_ptr] & ~bit_block(bit(b), n_bits));
  
      n_bits -= bits_per_word - bit(b);
      word_ptr++;
      size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
      for (; word_ptr < last_word; word_ptr++){
        bits[word_ptr] = (word_t)(bits[word_ptr] & ~bit_block(0, n_bits));
        n_bits -= bits_per_word;
      }
    }
  
    inline void flip (size_t b){
      bits[word(b)] = (word_t)(bits[word(b)] ^  (word_t(1) << (bit(b))));
    }
  
    inline void flip (size_t b, size_t e){
      size_t word_ptr = word(b);
      size_t n_bits = e - b;
  
      bits[word_ptr] = (word_t)(bits[word_ptr] ^ bit_block(bit(b), n_bits));
  
      n_bits -= bits_per_word - bit(b);
      word_ptr++;
      size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
      for (; word_ptr < last_word; word_ptr++){
        bits[word_ptr] = (word_t)(bits[word_ptr] ^ bit_block(0, n_bits));
        n_bits -= bits_per_word;
      }
    }
  
    inline bool test  (size_t b) const {
      return (bits[word(b)] & (word_t(1) << (bit(b))));
    }
  
    inline size_t ffs(size_t b = 0, size_t e = S) const {
  #if defined(FERRET_BITSET_USE_COMPILER_INTRINSICS)
        // search first word
        size_t word_ptr = word(b);
        word_t this_word = bits[word_ptr];
  
        // mask off bits below bound
        this_word &= (~static_cast<word_t>(0)) << bit(b);
        
        if (this_word != static_cast<word_t>(0))
  	return ((word_ptr * bits_per_word) + (size_t) __builtin_ctz(this_word));
  
        // check subsequent words
        word_ptr++;
        size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
        for (; word_ptr < last_word; word_ptr++){
          this_word = bits[word_ptr];
          if (this_word != static_cast<word_t>(0))
            return ((word_ptr * bits_per_word) + (size_t) __builtin_ctz(this_word));
        }
  #else
        for(size_t i = b; i < e; i++)
          if (test(i))
            return i;
  #endif
      return S;
    }
  
    inline size_t ffr(size_t b = 0, size_t e = S) const {
  #if defined(FERRET_BITSET_USE_COMPILER_INTRINSICS)
        // same as ffs but complements word before counting
        size_t word_ptr = word(b);
        word_t this_word = ~bits[word_ptr];
  
        this_word &= (~static_cast<word_t>(0)) << bit(b);
        
        if (this_word != static_cast<word_t>(0))
  	return ((word_ptr * bits_per_word) + (size_t) __builtin_ctz(this_word));
  
        word_ptr++;
        size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
        for (; word_ptr < last_word; word_ptr++){
          this_word = ~bits[word_ptr];
          if (this_word != static_cast<word_t>(0))
            return ((word_ptr * bits_per_word) + (size_t) __builtin_ctz(this_word));
        }
  #else
        for(size_t i = b; i < e; i++)
          if (!test(i))
            return i;
  #endif
      return S;
    }
  
    // Return word with length-n bit block starting at bit p set.
    // Both p and n are effectively taken modulo bits_per_word.
    static inline word_t bit_block(size_t p, size_t n){
      if (n >= bits_per_word)
        return (word_t)(word_t(-1) << p);
  
      word_t x = (word_t)((word_t(1) << n) - word_t(1));
      return  (word_t)(x << p);
    }
  
  #if defined(FERRET_STD_LIB)
    friend std::ostream& operator<< (std::ostream& stream, bitset& x) {
      for(size_t i = 0; i < S; i++)
        stream << x.test(i);
      return stream;
    }
  #endif
  };
}

// Math
namespace ferret{
  constexpr auto operator "" _MB( unsigned long long const x ) -> long {
    return 1024L * 1024L * (long)x;
  }
  
  constexpr auto operator "" _KB( unsigned long long const x ) -> long {
    return 1024L * (long)x;
  }
  
  constexpr auto operator "" _pi(long double x) -> double {
    return 3.14159265358979323846 * (double)x;
  }
  
  constexpr auto operator "" _pi(unsigned long long int  x) -> double {
    return 1.0_pi * (double)x;
  }
  
  constexpr auto operator "" _deg(long double x) -> double {
    return (1.0_pi * (double)x) / 180;
  }
  
  constexpr auto operator "" _deg(unsigned long long int  x) -> double {
    return 1.0_deg * (double)x;
  }
  #if !defined(__clang__)
  constexpr auto operator "" _QN(long double x) -> int {
    return (int)::floor(::log(1.0/(double)x)/::log(2));
  }
  #endif
  
  template<int bits> struct fixed_real_container;
  template<> struct fixed_real_container<8>  { typedef int8_t  base_type;
                                               typedef int16_t next_type; };
  template<> struct fixed_real_container<16> { typedef int16_t base_type;
                                               typedef int24_t next_type; };
  template<> struct fixed_real_container<24> { typedef int24_t base_type;
                                               typedef int32_t next_type; };
  template<> struct fixed_real_container<32> { typedef int32_t base_type;
                                               typedef int64_t next_type; };
  template<> struct fixed_real_container<64> { typedef int64_t base_type;
                                               typedef int64_t next_type; };
  
  #pragma pack(push, 1)
  template<int bits, int exp>
  class fixed_real {
    typedef fixed_real fixed;
    typedef typename fixed_real_container<bits>::base_type base;
    typedef typename fixed_real_container<bits>::next_type next;
  
    base m;
    static const int N      = (exp - 1);
    static const int factor = 1 << N;
  
    template<typename T>
    inline base from(T d) const { return (base)(d * factor); }
  
    template<typename T>
    inline T to_rational() const { return T(m) / factor; }
  
    template<typename T>
    inline T to_whole() const { return (T)(m >> N); }
  
  public:
  
    //from types
    explicit fixed_real( )           : m(0) { }
    template<typename T>
    explicit fixed_real(T v)         : m(from<T>(v)) {}
  
    template<typename T>
    fixed& operator=(T v)        { m = from<T>(v); return *this; }
  
    //to types
    template<typename T>
    operator T()           const { return to_whole<T>();    }
    operator double()      const { return to_rational<double>(); }
  
    // operations
    fixed& operator+= (const fixed& x) { m += x.m; return *this; }
    fixed& operator-= (const fixed& x) { m -= x.m; return *this; }
    fixed& operator*= (const fixed& x) { m = (base)(((next)m * (next)x.m) >> N); return *this; }
    fixed& operator/= (const fixed& x) { m = (base)(((next)m * factor) / x.m); return *this; }
    fixed& operator*= (int x)          { m *= x; return *this; }
    fixed& operator/= (int x)          { m /= x; return *this; }
    fixed  operator-  ( )              { return fixed(-m); }
  
    // friend functions
    friend fixed operator+ (fixed x, const fixed& y) { return x += y; }
    friend fixed operator- (fixed x, const fixed& y) { return x -= y; }
    friend fixed operator* (fixed x, const fixed& y) { return x *= y; }
    friend fixed operator/ (fixed x, const fixed& y) { return x /= y; }
  
    // comparison operators
    friend bool operator== (const fixed& x, const fixed& y) { return x.m == y.m; }
    friend bool operator!= (const fixed& x, const fixed& y) { return x.m != y.m; }
    friend bool operator>  (const fixed& x, const fixed& y) { return x.m > y.m; }
    friend bool operator<  (const fixed& x, const fixed& y) { return x.m < y.m; }
    friend bool operator>= (const fixed& x, const fixed& y) { return x.m >= y.m; }
    friend bool operator<= (const fixed& x, const fixed& y) { return x.m <= y.m; }
  
  #if defined(FERRET_STD_LIB)
    friend std::ostream& operator<< (std::ostream& stream, const fixed& x) {
      stream << (double)x;
      return stream;
    }
  #endif
  };
  #pragma pack(pop)
  #if !defined(FERRET_NUMBER_TYPE)
     #define FERRET_NUMBER_TYPE int
  #endif
  
  #if !defined(FERRET_REAL_TYPE)
     #define FERRET_REAL_TYPE   double
  #endif
  
  #if !defined(FERRET_REAL_EPSILON)
     #define FERRET_REAL_EPSILON   0.0001
  #endif
  
    int req_real_precision(double t) {
      return ((-1 * (int)log10(t)));
    }
  
    typedef FERRET_NUMBER_TYPE  number_t;                   // Whole number Container.
    typedef FERRET_REAL_TYPE    real_t;                     // Real number Container.
    const   real_t              real_epsilon(FERRET_REAL_EPSILON);
    const   int                 real_precision = req_real_precision(FERRET_REAL_EPSILON);
  namespace runtime{
    #undef min
    #undef max
    #undef abs
  
    template <typename T>
    static constexpr T max(T a, T b) {
      return a < b ? b : a;
    }
  
    template <typename T, typename... Ts>
    static constexpr T max(T a, Ts... bs) {
      return max(a, max(bs...));
    }
  
    template<typename T>
    constexpr T min(T a, T b){
      return ((a) < (b) ? (a) : (b));
    }
  
    template <typename T, typename... Ts>
    static constexpr T min(T a, Ts... bs) {
      return min(a, min(bs...));
    }
  
    template<typename T>
    constexpr T abs(T a){
      return ((a) < (T)0 ? -(a) : (a));
    }
  }
}

// Initialize Hardware
namespace ferret{
  #if !defined(FERRET_UART_RATE)
    # define FERRET_UART_RATE 9600
  #endif
  #if !defined(FERRET_IO_STREAM_SIZE)
    # define FERRET_IO_STREAM_SIZE 80
  #endif
  #if defined(FERRET_DISABLE_STD_OUT)
     namespace runtime{
       void init(){ }
  
       template <typename T>
       void print(T){ }
     }
  #endif
  #if defined(FERRET_STD_LIB) && !defined(FERRET_DISABLE_STD_OUT)
    namespace runtime{
      void init(){}
  
      template <typename T>
      void print(const T & t){ std::cout << t; }
  
      template <>
      void print(const real_t & n){
        std::cout << std::fixed << std::setprecision(real_precision) << n;
      }
  
      void read_line(char *buff, std::streamsize len){
        std::cin.getline(buff, len);
      }
    }
  #endif
  #if defined(FERRET_HARDWARE_ARDUINO) && !defined(FERRET_DISABLE_STD_OUT) 
    namespace runtime{
      void init(){ FERRET_HARDWARE_ARDUINO_UART_PORT.begin(FERRET_UART_RATE); }
  
      template <typename T>
      void print(const T t){ FERRET_HARDWARE_ARDUINO_UART_PORT.print(t); }
  
      template <>
      // cppcheck-suppress passedByValue
      void print(const real_t d){
        FERRET_HARDWARE_ARDUINO_UART_PORT.print(double(d), real_precision);
      }
  
      template <>
      void print(void *p){
        FERRET_HARDWARE_ARDUINO_UART_PORT.print((size_t)p,HEX);
      }
  
      template <> void print(const void * const p){
        FERRET_HARDWARE_ARDUINO_UART_PORT.print((size_t)p, HEX);
      }
  
      void read_line(char *buff, size_t len){
        byte idx = 0;
        char c;
        do{
          while (FERRET_HARDWARE_ARDUINO_UART_PORT.available() == 0);
          c = FERRET_HARDWARE_ARDUINO_UART_PORT.read();
          buff[idx++] = c;
        }while (c != '\n');
        buff[--idx] = 0x00;
      }
     }
  #endif
  #if !defined(FERRET_DISABLE_STD_OUT)
     namespace runtime{
       template <typename T>
       void println(T t){
         print(t);
         print((char)0xA);
       }
     }
  #endif
}

// Object System Base
namespace ferret{
  namespace memory {
    template <typename T>
    class pointer{
      T *ptr;
  
    public:
  
      inline explicit pointer(T *p = nullptr) : ptr(p){ }
      inline operator T* () const { return ptr; }
  
      inline pointer& operator= (T *other){
        ptr = other;
        return *this;
      }
  
      inline T *operator->() const { return ptr; }
    };
  }
  namespace memory{
    inline size_t align_of(uintptr_t size, size_t align){
      return (size + align - 1) & ~(align - 1);
    }
  
    template<class T>
    size_t align_of(const void * ptr) {
      return align_of(reinterpret_cast<uintptr_t>(ptr), sizeof(T));
    }
  
    inline size_t align_req(uintptr_t size, size_t align){
      size_t adjust = align - (size & (align - 1));
  
      if(adjust == align)
        return 0;
      return adjust;
    }
  
    template<class T>
    size_t align_req(const void * ptr) {
      return align_req(reinterpret_cast<uintptr_t>(ptr), sizeof(T));
    }
  
    template <typename... Ts>
    constexpr size_t max_sizeof() {
      return rt::max(sizeof(Ts)...);
    }
  }
  #ifdef FERRET_MEMORY_POOL_SIZE
  namespace memory{
    namespace allocator{
      template<typename page_t, size_t pool_size,
               typename bitset_word_t = FERRET_BITSET_WORD_TYPE>
      struct memory_pool {
        bitset<pool_size, bitset_word_t> used;
        page_t pool[pool_size];
        size_t next_ptr;
  
        memory_pool() : pool{0}, next_ptr(0) { }
  
        inline size_t scan(size_t n_pages, size_t from_page = 0) const {
          for(;;){
            size_t begin = used.ffr(from_page);
            size_t end   = begin + n_pages;
  
            if (end > pool_size)
              return pool_size;
  
            if (used.ffs(begin, end) >= end)
              return begin;
  
            from_page = end;
          }
        }
  
        void *allocate(size_t req_size){
          req_size = align_of(req_size, sizeof(page_t)) + sizeof(page_t);
          size_t n_pages = req_size / sizeof(page_t);
          size_t page   = scan(n_pages, next_ptr);
  
          if (page == pool_size){
            page = scan(n_pages);
            if (page == pool_size)
              return nullptr;
          }
  
          pool[page] = (page_t)n_pages;
          next_ptr = page + n_pages;
          used.flip(page, next_ptr);
  
          return &pool[++page];
        }
  
        void free(void *p){
          ptrdiff_t begin = (static_cast<page_t *>(p) - pool) - 1;
          ptrdiff_t end = begin + (ptrdiff_t)pool[begin];
          used.flip((size_t)begin, (size_t)end);
        }
      };
    }
  }
  #endif
  #if defined(FERRET_MEMORY_POOL_SIZE) && !defined(FERRET_ALLOCATOR)
  
   #define FERRET_ALLOCATOR memory::allocator::pool
  
   #if !defined(FERRET_MEMORY_POOL_PAGE_TYPE)
    #define FERRET_MEMORY_POOL_PAGE_TYPE size_t
   #endif
  
  namespace memory{
    namespace allocator{
  
      memory_pool<FERRET_MEMORY_POOL_PAGE_TYPE, FERRET_MEMORY_POOL_SIZE> program_memory;
  
      class pool{
      public:
  
        static void init(){ }
  
        static inline void*  allocate(size_t s){
          return program_memory.allocate(s);
        }
  
        template<typename FT>
        static inline void* allocate(){ return allocate(sizeof(FT)); }
  
        static inline void   free(void * ptr){ program_memory.free(ptr); }
      };
    }
  }
  #endif
  #ifdef FERRET_MEMORY_BOEHM_GC
  
  #define FERRET_ALLOCATOR memory::allocator::gc
  #define FERRET_DISABLE_RC true
  
  #include <gc.h>
  
  namespace memory{
    namespace allocator{
  
      class gc{
      public:
  
        static void init(){ GC_INIT(); }
  
        static inline void* allocate(size_t s){
  #ifdef FERRET_DISABLE_MULTI_THREADING
          return GC_MALLOC(s);
  #else
          return GC_MALLOC_ATOMIC(s);
  #endif
        }
  
        template<typename FT>
        static inline void* allocate(){ return allocate(sizeof(FT)); }
  
        static inline void  free(void * ptr){ }
      };
    }
  }
  #endif
  #if !defined(FERRET_ALLOCATOR)
  
  #define FERRET_ALLOCATOR memory::allocator::system
  
  namespace memory{
    namespace allocator{
  
      class system{
      public:
  
        static void init(){ }
  
        static inline void* allocate(size_t s){ return ::malloc(s); }
  
        template<typename FT>
        static inline void* allocate(){ return allocate(sizeof(FT)); }
  
        static inline void  free(void * ptr){ ::free(ptr); } 
      };
    }
  }
  #endif
  namespace memory{
    namespace allocator{
      class synchronized{
        static mutex lock;
      public:
  
        static void init(){ FERRET_ALLOCATOR::init(); }
  
        static inline void* allocate(size_t s){
          lock_guard guard(lock);
          return FERRET_ALLOCATOR::allocate(s);
        }
  
        template<typename FT>
        static inline void* allocate(){ return allocate(sizeof(FT)); }
  
        static inline void  free(void * ptr){
          lock_guard guard(lock);
          FERRET_ALLOCATOR::free(ptr);
        }
      };
    }
  }
  #if  !defined(FERRET_DISABLE_MULTI_THREADING)
  
    #if defined(FERRET_MEMORY_POOL_SIZE) || defined(FERRET_HARDWARE_ARDUINO)
      mutex memory::allocator::synchronized::lock;
      #undef  FERRET_ALLOCATOR
      #define FERRET_ALLOCATOR memory::allocator::synchronized
    #endif
  
  #endif
  #if !defined(FERRET_RC_POLICY)
  namespace memory {
    namespace gc {
  
  #if !defined(FERRET_RC_TYPE)
    #define FERRET_RC_TYPE unsigned int
  #endif
  
  #if defined(FERRET_DISABLE_RC)
  
  #define FERRET_RC_POLICY memory::gc::no_rc
  
      class no_rc{
      public:
  
        inline void inc_ref() { }
        inline bool dec_ref() { return false; }
      };
  
  #else
  
      template<typename T>
      class rc{
      public:
        rc() : ref_count(0) {}
  
        inline void inc_ref() { ref_count++; }
        inline bool dec_ref() { return (--ref_count == 0); }
  
      private:
        T ref_count;
      };    
  
      #if defined(FERRET_DISABLE_MULTI_THREADING) || !defined(FERRET_STD_LIB)
        #define FERRET_RC_POLICY memory::gc::rc<FERRET_RC_TYPE>
      #endif
  
      #if defined(FERRET_STD_LIB) && !defined(FERRET_DISABLE_MULTI_THREADING)
        #define FERRET_RC_POLICY memory::gc::rc<::std::atomic<FERRET_RC_TYPE>>
      #endif
  #endif
    }
  }
  #endif
  template<typename>
  void type_id(){}
  
  using type_id_t = void(*)();
  typedef type_id_t type_t;
  
  class var;
  typedef var const & ref;
  class seekable_i;
  
  template <typename rc>
  class object_i : public rc{
  public:
    object_i() { }
    virtual ~object_i() { };
  
    virtual type_t type() const = 0;
  
  #if !defined(FERRET_DISABLE_STD_OUT)
    virtual void stream_console() const {
      rt::print("var#");
      const void* addr = this;
      rt::print(addr);
    }
  #endif
  
    virtual bool equals(ref) const;
  
    virtual seekable_i* cast_seekable_i() { return nullptr; }
  
    void* operator new(size_t, void* ptr){ return ptr; }
    void  operator delete(void * ptr){ FERRET_ALLOCATOR::free(ptr); }
  };
  
  typedef object_i<FERRET_RC_POLICY> object;
  #if !defined(FERRET_POINTER_T)
    #define FERRET_POINTER_T memory::pointer<object>
  #endif
  
  typedef FERRET_POINTER_T pointer_t;
  class var{
  public:
    explicit inline var(object* o = nullptr) : obj(o) { inc_ref(); }
    inline var(ref o)   : obj(o.obj) { inc_ref(); }
    inline var(var&& o) : obj(o.detach()) { }
  
    ~var() { dec_ref(); }
  
    inline var& operator=(var&& other){
      if (this != &other){
        dec_ref();
        obj = other.detach();
      }
      return *this;
    }
  
    inline var& operator= (ref other){
      if (obj != other.obj){
        dec_ref();
        obj = other.obj;
        inc_ref();
      }
      return *this;
    }
  
    bool equals (ref) const;
  
    bool operator==(ref other) const { return equals(other); }
  
    bool operator!=(ref other) const { return !equals(other); }
  
    void* operator new(size_t, void* ptr){ return ptr; }
  
    operator bool() const;
  
  #if !defined(FERRET_DISABLE_STD_OUT)
    void stream_console() const {
      if (obj != nullptr )
        obj->stream_console();
      else
        rt::print("nil");
    }
  #endif
  
    inline object* get() const { return obj; }
  
    template<typename T>
    inline T* cast() const { return static_cast<T*>((object*)obj); }
  
    inline bool is_type(type_t type) const {
      if (obj)
        return (static_cast<object*>(obj)->type() == type);
      return false;
    }
  
    inline bool is_nil() const { return (obj == nullptr); }
  
  private:
    object* detach(){
      object* _obj = obj;
      obj = nullptr;
      return _obj;
    }
  
    inline void inc_ref(){
  #if !defined(FERRET_DISABLE_RC)
      // Only change if non-null
      if (obj) obj->inc_ref();
  #endif
    }
  
    inline void dec_ref(){
  #if !defined(FERRET_DISABLE_RC)
      // Only change if non-null
      if (obj){
        // Subtract and test if this was the last pointer.
        if (obj->dec_ref()){
          delete obj;
          obj = nullptr;
        }
      }
  #endif
    }
  
    pointer_t obj;
  };
  
  template<>
  inline seekable_i* var::cast<seekable_i>() const { return obj->cast_seekable_i(); }
  
  template <typename rc>
  bool object_i<rc>::equals(ref o) const {
    return (this == o.get());
  }
  
  #ifdef FERRET_STD_LIB
  std::ostream &operator<<(std::ostream &os, var const &v) {
    v.stream_console();
    return os;
  }
  #endif
  template<typename FT, typename... Args>
  inline var obj(Args... args) {
    void * storage = FERRET_ALLOCATOR::allocate<FT>();
    return var(new(storage) FT(args...));
  }
  
  inline var nil(){
    return var();
  }
  #undef alloca
  
  template<typename T>
  class alloca {
  
    byte memory [sizeof(T)];
    
  public:
    
    template<typename... Args>
    inline explicit alloca(Args... args) {
      (new(memory) T(args...))->inc_ref();
    }
  
    inline operator object*() {
      return (object*)memory;
    }
  };
  
}

namespace ferret{
  template <typename T>
  class array {
    size_t  _size{0};
  
  public:
  
    T* data {nullptr};
  
    explicit inline array(size_t s = 0) : _size(s) {
      data = (T *)FERRET_ALLOCATOR::allocate(_size * sizeof(T));
    }
  
    explicit inline array(const T* source, size_t s = 0) : _size(s) {
      data = (T *)FERRET_ALLOCATOR::allocate(_size * sizeof(T));
      for(size_t i = 0; i < _size; i++)
        data[i] = source[i];
    }
  
  #if defined(FERRET_STD_LIB)
    explicit inline array(std::initializer_list<T> source) :
      _size(source.size()) {
      data = (T *)FERRET_ALLOCATOR::allocate(_size * sizeof(T));
      size_t idx = 0;
      for(auto item : source){  
        data[idx] = item;
        idx++;
      }
    }
  #endif
  
    inline array(array&& m) :
      data(m.data), _size(m.size()) { m.data = nullptr; }
  
    inline array(array& m) : _size(m.size()){
      for(size_t i = 0; i < _size; i++)
        data[i] = m.data[i];
    }
    
    ~array(){
      FERRET_ALLOCATOR::free(data);
    }
  
  
    inline array& operator=(array&& x){
      data = x.data;
      _size = x._size;
      x.data = nullptr;
      return *this;
    }
  
    inline T& operator [](size_t idx)      { return data[idx]; }
    inline T operator [](size_t idx) const { return data[idx]; }
  
    inline T*      begin() const { return &data[0];      }
    inline T*      end()   const { return &data[_size];  }
    inline size_t  size()  const { return _size;         }
  };
  class matrix {
    //row-major
    array<real_t> data;
    //shape
    size_t  rows{0};
    size_t  cols{0};
  
    inline static void into_aux(matrix &){ }
  
    template<typename... Args>
    inline static void into_aux(matrix &m, real_t first, Args... rest){
      m.data[m.data.size() - sizeof...(rest) - 1] = first;
      into_aux(m, rest...);
    }
  
  public:
    inline matrix(size_t r = 0, size_t c = 0) :
      data(r * c), rows(r) , cols(c) { }
  
    template<typename... Args>
    inline matrix(size_t rows, size_t cols, Args... elements)
      : matrix(rows,cols) {
      into_aux(*this, elements...);
    }
  
    inline matrix(matrix&& m) :
      data(m.data), rows(m.rows), cols(m.cols) { }
  
    inline matrix(matrix& m)
      : matrix(m.rows,m.cols){
      for(size_t i = 0; i < data.size(); i++)
        data[i] = m.data[i];
    }
  
    inline matrix operator+ (const matrix& m) const {
      matrix sum(rows,cols);
      for(size_t i = 0; i < data.size(); i++)
        sum.data[i] = data[i] + m.data[i];
      return sum;
    }
  
    inline matrix operator- (const matrix& m) const {
      matrix diff(rows,cols);
      for(size_t i = 0; i < data.size(); i++)
        diff.data[i] = data[i] - m.data[i];
      return diff;
    }
  
    matrix operator* (const matrix& m) const {
      matrix mul = matrix::zeros(rows, m.cols);
  
      if (cols != m.rows)
        return mul;
  
      for (size_t i = 0; i < rows; i++) {
        for (size_t j = 0; j < m.cols; j++) {
          for (size_t k = 0; k < m.rows; k++) {
            mul(i,j, mul(i,j) + operator()(i,k) * m(k,j));
          }
        }
      }
  
      return mul;
    }
  
    matrix operator* (const real_t& val) const {
      matrix mul(rows,cols);
      for(size_t i = 0; i < data.size(); i++)
        mul.data[i] = data[i] * val;
      return mul;
    }
  
    inline real_t operator()(size_t row, size_t col) const {
      return data[row * cols + col];
    }
  
    inline void operator()(size_t row, size_t col, real_t val) {
      data[row * cols + col] = val;
    }
  
    inline matrix& operator=(matrix&& x){
      data = array<real_t>(x.data);
      rows = x.rows;
      cols = x.cols;
      return *this;
    }
  
    inline bool operator ==(const matrix& m) const {
      for (size_t i = 0; i < data.size(); i++)
        if (data[i] != m.data[i])
          return false;
      return true;
    }
  
  #if defined(FERRET_STD_LIB)
    friend std::ostream& operator<< (std::ostream& stream, const matrix& x) {
      stream << "[";
      for (size_t r = 0; r < x.rows; r++){
        stream << "[";
        stream << x(r, 0);
        for (size_t c = 1; c < x.cols; c++)
          stream << " " << x(r,c);
        stream << "]";
      }
      return stream << "]";
    }
  #endif
  
    inline static matrix empty(size_t r = 0, size_t c = 0) {
      return matrix(r,c);
    }
  
    inline static void fill(matrix& m, real_t val) {
      for(size_t i = 0; i < m.data.size(); i++)
        m.data[i] = val;
    }
    
    inline static matrix zeros(size_t r = 0, size_t c = 0) {
      matrix m(r,c);
      fill(m, real_t(0));
      return m;
    }
  
    inline static matrix ones(size_t r = 0, size_t c = 0) {
      matrix m(r,c);
      fill(m, real_t(1));
      return m;
    }
  
    inline static matrix full(size_t r = 0, size_t c = 0, real_t v = real_t(0)) {
      matrix m(r,c);
      fill(m, v);
      return m;
    }
  
    static matrix eye(size_t n = 1){
      matrix m = matrix::zeros(n,n);
  
      for(size_t r = 0; r < m.rows; r++)
        m(r,r,real_t(1));
  
      return m;
    }
  
    template<size_t rows, size_t cols, typename... Args>
    inline static matrix into(Args... rest){
      matrix m(rows, cols);
      into_aux(m, rest...);
      return m;
    }
  
    inline static size_t row_count(const matrix& m){
      return m.rows;
    }
  
    inline static size_t column_count(const matrix& m){
      return m.cols;
    }
  
    static real_t norm_euclidean(const matrix& m){
      real_t norm = real_t(0);
  
      for(size_t i = 0; i < m.data.size(); i++){
        norm += m.data[i] * m.data[i];
      }
  
      return real_t(sqrt((double)norm));
    }
  
    static matrix normalise(const matrix& m){
      real_t mag = matrix::norm_euclidean(m);
      matrix norm = matrix::zeros(m.rows,m.cols);
  
      if (mag == real_t(0))
        return norm;
  
      for(size_t i = 0; i < m.data.size(); i++)
        norm.data[i] = m.data[i] / mag;
  
      return norm;
    }
  };
}

// Runtime Prototypes
namespace ferret{
    namespace runtime {
      var list(ref v);
      template <typename... Args>
      var list(ref first, Args const & ... args);
  
      inline bool is_seqable(ref seq);
  
      inline var first(ref seq);
      inline var rest(ref seq);
      inline var cons(ref x, ref seq);
  
      var nth(var seq, number_t index);
      var nthrest(var seq, number_t index);
  
      inline size_t count(ref seq);
  
      inline var range(number_t low, number_t high);
    }
  
  #define for_each(x,xs) for(var _tail_ = rt::rest(xs), x = rt::first(xs);     \
                             !_tail_.is_nil();                                 \
                             x = rt::first(_tail_), _tail_ = rt::rest(_tail_))
  template<typename T, typename... Args>
  inline var run(T const & fn, Args const & ... args);
  
  template<typename T>
  inline var run(T const & fn);
  
  template<>
  inline var run(ref);
  
  namespace runtime{
    inline var apply(ref fn, ref argv);
  }
}
