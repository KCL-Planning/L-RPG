#include <iostream>
#include <assert.h>

#include "logging.h"

namespace MyPOP {

namespace Logging {

LogLevel verbosity = INFO;

void setLogLevel(int log_level)
{
	switch (log_level)
	{
		case 0:
			verbosity = DEBUG;
			break;
		case 1:
			verbosity = INFO;
			break;
		case 2:
			verbosity = WARNING;
			break;
		case 3:
			verbosity = ERROR;
			break;
		default:
			std::cout << "Unknown debug level " << log_level << std::endl;
			assert(false);
	}
}

};

};
