#if !defined(ERMINE_DISABLE_STD_MAIN)
 #if defined(ERMINE_DISABLE_CLI_ARGS) || !defined(ERMINE_STD_LIB)
  int main()
 #else
  int main(int argc, char* argv[])
 #endif
  {     
    using namespace ermine;
    ERMINE_ALLOCATOR::init();
    rt::init();

   #if defined(ERMINE_STD_LIB) && !defined(ERMINE_DISABLE_CLI_ARGS)
    for (int i = argc - 1; i > -1 ; i--)
      _star_command_line_args_star_ =  rt::cons(obj<string>(argv[i]),_star_command_line_args_star_);
   #endif

    $file$::main();

   #if defined(ERMINE_PROGRAM_MAIN)
    run(ERMINE_PROGRAM_MAIN);
   #endif

    return 0;
  }
#endif
#if defined(ERMINE_HARDWARE_ARDUINO)
  void setup(){
    using namespace ermine;
    ERMINE_ALLOCATOR::init();
    rt::init();

    #if defined(ERMINE_PROGRAM_MAIN)
      $file$::main();
    #endif
  }

  void loop(){
    using namespace ermine;
    #if !defined(ERMINE_PROGRAM_MAIN)
      $file$::main();
    #endif          

    #if defined(ERMINE_PROGRAM_MAIN)
      run(ERMINE_PROGRAM_MAIN);
    #endif
  }
#endif
