include "console.iol"
include "file.iol"

type ProcessRequest: void {
  .specification: string
  .context: string // in JSON format
}

type ProcessResponse: void {
  .configuration: string  //in JSON format
}

interface ReconfiguratorInterface {
RequestResponse:
  process( ProcessRequest )( ProcessResponse )
}

outputPort ReconfiguratorService {
    Location: "socket://localhost:9000"
    Protocol: http { .method = "get" } 
    Interfaces: ReconfiguratorInterface
}

main {
	
	readfile_request.filename = "test_context.txt";
	readFile@File(readfile_request)(request.context);

	readfile_request.filename = "test_fm.txt";
	readFile@File(readfile_request)(request.specification);
	
	process@ReconfiguratorService(request)(response);
	println@Console( response.configuration )()
}
