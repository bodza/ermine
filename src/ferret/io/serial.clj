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
