#ifndef MYPOP_LOGGING
#define MYPOP_LOGGING

/**
 * This class takes care of the logging of messages. We declare 4 levels of logging:
 * DEBUG: These include messages one is only interested while debugging the application.
 * INFO: Messages which are shown when one is interested in why decisions are made.
 * WARNING: Messages which are shown indicating there is a potential problem.
 * ERROR: Messages which are shown when a fatal error occured. The program should terminate
 * after encountering an error message.
 */
namespace MyPOP {

namespace Logging {

enum LogLevel { DEBUG, INFO, WARNING, ERROR };
const std::string LogLevelString[4] =  { "DEBUG", "INFO", "WARNING", "ERROR" };

extern LogLevel verbosity;
void setLogLevel(int log_level);

};

};

#endif
