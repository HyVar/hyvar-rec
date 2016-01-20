include "console.iol"
include "exec.iol"
include "math.iol"
include "file.iol"

execution { concurrent }


type ProcessRequest: void {
  .specification: string
  .context: string
}

type ProcessResponse: void {
  .configuration: string
}

interface ReconfiguratorInterface {
RequestResponse:
  process( ProcessRequest )( ProcessResponse )
}

inputPort ReconfiguratorService {
    Location: "socket://localhost:9001"
    Protocol: http 
    Interfaces: ReconfiguratorInterface
}


main {
	[ process( request )( response ) {
		// Save files
		random@Math()(num);
		context_file = "/tmp/" + string(num) + ".context";
		spec_file = "/tmp/" + string(num) + ".txt";
		write_file_request.content = request.specification;
		write_file_request.filename = spec_file;
		writeFile@File(write_file_request)();
		write_file_request.content = request.context;
		write_file_request.filename = context_file;
		writeFile@File(write_file_request)();

		// Run command
		command_request = "python";
  	command_request.args[0] = "hyvar-rec.py";
		command_request.args[1] = spec_file;
		command_request.args[2] = context_file;
		exec@Exec( command_request )( output );
		println@Console( "exit code: " + string(output.exitCode) )();
		println@Console( "stderr: " + string(output.stderr) )();
  	response.configuration = string(output)
	} ] {nullProcess}
}
