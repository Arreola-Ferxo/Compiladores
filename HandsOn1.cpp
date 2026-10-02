// ================================================================================
// Hands-on 1: Analisis Lexico y Automatas
// Autor: Fernando de Jesús Arreola Reyes
// --------------------------------------------------------------------------------
// Estructura del programa:
//   1. AFD            -> valida caracter por caracter y produce tokens
//   2. Objeto instr.  -> se construye a partir de los tokens generados por el AFD 
//   3. Maquina Moore  -> recorre estados y va emitiendo microoperaciones
//   4. main / usuario -> entrada/salida
// ================================================================================

#include <iostream>
#include <string>
#include <vector>
#include <cctype>

using namespace std;

// Utilidades
// Preparamos el string para que no tenga espacios, ni tenga tabs al inicio ni al final. 
// asegurandonos de que no esté vacio ni sea negativo.
static string trim(const string& s) {
    size_t inicio = 0, fin = s.size();
    while (inicio < fin && isspace(static_cast<unsigned char>(s[inicio]))) inicio++;
    while (fin > inicio && isspace(static_cast<unsigned char>(s[fin - 1]))) fin--;
    return s.substr(inicio, fin - inicio); // devuelve la subcadena obtenida sin espacios al inicio ni al final
}

// SECCION 1: Tokens y AFD
enum class TipoToken { MOV, ADD, STO, END, REGISTRO, COMA, NUMERO };

struct Token {
    TipoToken tipo;
    string lexema;
};

// Función que devuelve el nombre del token como string
static string nombreToken(TipoToken t) {
    switch (t) {
        case TipoToken::MOV: return "MOV";
        case TipoToken::ADD: return "ADD";
        case TipoToken::STO: return "STO";
        case TipoToken::END: return "END";
        case TipoToken::REGISTRO: return "REGISTRO";
        case TipoToken::COMA: return "COMA";
        case TipoToken::NUMERO: return "NUMERO";
    }
    return "?";
}

// Estados del AFD. Cada mnemonico tiene su propia rama de estados, de modo
// que las transiciones (y por lo tanto los errores) queden explicitas.
enum EstadoAFD {
    Q0, // estado inicial
    
    // Rama MOV
    Q_M, Q_MO, Q_MOV, Q_MOV_ESP, // Estados para el mnemonico MOV y los espacios
    Q_MOV_R_A, Q_MOV_R_AL, Q_MOV_R_B, Q_MOV_R_BL, // Estados para el registro (AL o BL)
    Q_MOV_ESP2, Q_MOV_COMA, Q_MOV_ESP3, Q_MOV_NUM, // Estados para la coma y la dirección
    
    // Rama ADD
    Q_A, Q_AD, Q_ADD, Q_ADD_ESP, // Estados para el mnemonico ADD y los espacios
    Q_ADD_A, Q_ADD_AL, Q_ADD_ESP2, Q_ADD_COMA, Q_ADD_ESP3, // Estados para el registro AL, 
    Q_ADD_B, Q_ADD_BL,                                     // la coma y el registro BL
    
    // Rama STO
    Q_S, Q_ST, Q_STO, Q_STO_ESP, Q_STO_NUM, // Estados para el mnemonico STO, los espacios y la dirección
    
    // Rama END
    Q_E, Q_EN, Q_END,
    
    // Estado de error (estado trampa)
    Q_ERROR
};

// Descripcion de lo que el AFD espera encontrar desde cada estado.
// Se usa tanto si el error ocurre a media cadena como si la cadena
// termina antes de llegar a un estado de aceptacion.
static string esperadoEn(EstadoAFD e) {
    switch (e) {
        case Q0: return "un instruccion valida (MOV, ADD, STO o END)";
        case Q_M: return "'O' para completar el mnemonico MOV";
        case Q_MO: return "'V' para completar el mnemonico MOV";
        case Q_MOV: return "un espacio seguido de un registro (AL o BL)";
        case Q_MOV_ESP: return "un espacio";
        case Q_MOV_R_A: return "'L' para completar el registro AL";
        case Q_MOV_R_B: return "'L' para completar el registro BL";
        case Q_MOV_R_AL:
        case Q_MOV_R_BL:
        case Q_MOV_ESP2: return "una coma seguida de la direccion de memoria";
        case Q_MOV_COMA:
        case Q_MOV_ESP3: return "la direccion de memoria (un numero)";
        case Q_MOV_NUM: return "el fin de la instruccion (no se permiten mas caracteres)";

        case Q_A: return "'D' para completar el mnemonico ADD";
        case Q_AD: return "'D' para completar el mnemonico ADD";
        case Q_ADD: return "un espacio seguido del registro AL";
        case Q_ADD_ESP: return "un espacio";
        case Q_ADD_A: return "'L' para completar el registro AL";
        case Q_ADD_AL:
        case Q_ADD_ESP2: return "una coma seguida del registro BL";
        case Q_ADD_COMA:
        case Q_ADD_ESP3: return "el registro BL";
        case Q_ADD_B: return "'L' para completar el registro BL";
        case Q_ADD_BL: // return "el fin de la instruccion (no se permiten mas caracteres)";

        case Q_S: return "'T' para completar el mnemonico STO";
        case Q_ST: return "'O' para completar el mnemonico STO";
        case Q_STO: return "un espacio seguido de la direccion de memoria";
        case Q_STO_ESP: return "un espacio";
        case Q_STO_NUM: return "el fin de la instruccion (no se permiten mas caracteres)";

        case Q_E: return "'N' para completar el mnemonico END";
        case Q_EN: return "'D' para completar el mnemonico END";
        case Q_END: return "el fin de la instruccion (END no admite operandos)";
        default: return "una entrada valida";
    }
}

class AFD {
public:
    // Recorre la entrada caracter por caracter. Si es valida, llena tokensOut
    // y retorna true. Si no es valida, llena mensajeError y retorna false.
    bool validar(const string& entrada, vector<Token>& tokensOut, string& mensajeError) {
        tokensOut.clear();

        EstadoAFD estado = Q0;
        EstadoAFD estadoAnterior = Q0;
        bool huboError = false;
        char caracterError = '\0';
        size_t posError = 0;

        // Indices de los lexemas que se van reconociendo durante el recorrido
        size_t mnemonico_inicio = 0, mnemonico_final = 0; 
        size_t registro_1_inicio = 0, registro_1_final = 0, registro_2_inicio = 0, registro_2_final = 0;
        size_t num_inicio = 0, num_final = 0;

        // recorre la cadena de entrada caracter por caracter, actualizando el estado
        size_t n = entrada.size();
        for (size_t i = 0; i < n; i++) {
            char c = entrada[i];
            estadoAnterior = estado;

            switch (estado) {
                // estado inicial: decide la rama segun la primera letra 
                case Q0:
                    if (c == 'M') { estado = Q_M; mnemonico_inicio = i; }
                    else if (c == 'A') { estado = Q_A; mnemonico_inicio = i; }
                    else if (c == 'S') { estado = Q_S; mnemonico_inicio = i; }
                    else if (c == 'E') { estado = Q_E; mnemonico_inicio = i; }
                    else estado = Q_ERROR;
                    break;

                // MOV 
                case Q_M: 
                    estado = (c == 'O') ? Q_MO : Q_ERROR; 
                    break;
                case Q_MO: 
                    if (c == 'V') { estado = Q_MOV; mnemonico_final = i; } 
                    else estado = Q_ERROR; 
                    break;
                case Q_MOV:
                    estado = isspace(static_cast<unsigned char>(c)) ? Q_MOV_ESP : Q_ERROR;
                    break;
                case Q_MOV_ESP:
                    if (isspace(static_cast<unsigned char>(c))) estado = Q_MOV_ESP;
                    else if (c == 'A') { estado = Q_MOV_R_A; registro_1_inicio = i; }
                    else if (c == 'B') { estado = Q_MOV_R_B; registro_1_inicio = i; }
                    else estado = Q_ERROR;
                    break;
                case Q_MOV_R_A: 
                    if (c == 'L') { estado = Q_MOV_R_AL; registro_1_final = i; } 
                    else estado = Q_ERROR; 
                    break;
                case Q_MOV_R_B: 
                    if (c == 'L') { estado = Q_MOV_R_BL; registro_1_final = i; } 
                    else estado = Q_ERROR; 
                    break;
                case Q_MOV_R_AL:
                case Q_MOV_R_BL:
                    if (isspace(static_cast<unsigned char>(c))) estado = Q_MOV_ESP2;
                    else if (c == ',') estado = Q_MOV_COMA;
                    else estado = Q_ERROR;
                    break;
                case Q_MOV_ESP2:
                    if (isspace(static_cast<unsigned char>(c))) estado = Q_MOV_ESP2;
                    else if (c == ',') estado = Q_MOV_COMA;
                    else estado = Q_ERROR;
                    break;
                case Q_MOV_COMA:
                    if (isspace(static_cast<unsigned char>(c))) estado = Q_MOV_ESP3;
                    else if (isdigit(static_cast<unsigned char>(c))) { estado = Q_MOV_NUM; num_inicio = num_final = i; }
                    else estado = Q_ERROR;
                    break;
                case Q_MOV_ESP3:
                    if (isspace(static_cast<unsigned char>(c))) estado = Q_MOV_ESP3;
                    else if (isdigit(static_cast<unsigned char>(c))) { estado = Q_MOV_NUM; num_inicio = num_final = i; }
                    else estado = Q_ERROR;
                    break;
                case Q_MOV_NUM:
                    if (isdigit(static_cast<unsigned char>(c))) { estado = Q_MOV_NUM; num_final = i; }
                    else estado = Q_ERROR; // no se permite nada más después del número
                    break;

                // ADD 
                case Q_A:  
                    estado = (c == 'D') ? Q_AD : Q_ERROR; 
                    break;
                case Q_AD: 
                    if (c == 'D') { estado = Q_ADD; mnemonico_final = i; } 
                    else estado = Q_ERROR; 
                    break;
                case Q_ADD:
                    estado = isspace(static_cast<unsigned char>(c)) ? Q_ADD_ESP : Q_ERROR;
                    break;
                case Q_ADD_ESP:
                    if (isspace(static_cast<unsigned char>(c))) estado = Q_ADD_ESP;
                    else if (c == 'A') { estado = Q_ADD_A; registro_1_inicio = i; }
                    else estado = Q_ERROR;
                    break;
                case Q_ADD_A: 
                    if (c == 'L') { estado = Q_ADD_AL; registro_1_final = i; } 
                    else estado = Q_ERROR; 
                    break;
                case Q_ADD_AL:
                    if (isspace(static_cast<unsigned char>(c))) estado = Q_ADD_ESP2;
                    else if (c == ',') estado = Q_ADD_COMA;
                    else estado = Q_ERROR;
                    break;
                case Q_ADD_B: 
                    if (c == 'L') { estado = Q_ADD_BL; registro_2_final = i; } 
                    else estado = Q_ERROR; 
                    break;
                case Q_ADD_BL:
                    if (isspace(static_cast<unsigned char>(c))) estado = Q_ADD_ESP2;
                    else if (c == ',') estado = Q_ADD_COMA;
                    else estado = Q_ERROR;
                    break;
                case Q_ADD_ESP2:
                    if (isspace(static_cast<unsigned char>(c))) estado = Q_ADD_ESP2;
                    else if (c == ',') estado = Q_ADD_COMA;
                    else estado = Q_ERROR;
                    break;
                case Q_ADD_COMA:
                    if (isspace(static_cast<unsigned char>(c))) estado = Q_ADD_ESP3;
                    else if (c == 'B') { estado = Q_ADD_B; registro_2_inicio = i; }
                    else estado = Q_ERROR;
                    break;
                case Q_ADD_ESP3:
                    if (isspace(static_cast<unsigned char>(c))) estado = Q_ADD_ESP3;
                    else if (c == 'B') { estado = Q_ADD_B; registro_2_inicio = i; }
                    else estado = Q_ERROR;
                    break;
                
                // STO 
                case Q_S:  
                    estado = (c == 'T') ? Q_ST : Q_ERROR; 
                    break;
                case Q_ST: 
                    if (c == 'O') { estado = Q_STO; mnemonico_final = i; } 
                    else estado = Q_ERROR; 
                    break;
                case Q_STO:
                    estado = isspace(static_cast<unsigned char>(c)) ? Q_STO_ESP : Q_ERROR;
                    break;
                case Q_STO_ESP:
                    if (isspace(static_cast<unsigned char>(c))) estado = Q_STO_ESP;
                    else if (isdigit(static_cast<unsigned char>(c))) { estado = Q_STO_NUM; num_inicio = num_final = i; }
                    else estado = Q_ERROR;
                    break;
                case Q_STO_NUM:
                    if (isdigit(static_cast<unsigned char>(c))) { estado = Q_STO_NUM; num_final = i; }
                    else estado = Q_ERROR;
                    break;

                // END 
                case Q_E:  
                    estado = (c == 'N') ? Q_EN  : Q_ERROR; 
                    break;
                case Q_EN: 
                    if (c == 'D') { estado = Q_END; mnemonico_final = i; } 
                    else estado = Q_ERROR; 
                    break;
                case Q_END:
                    estado = Q_ERROR; // END no admite ningun caracter adicional
                    break;

                default:
                    estado = Q_ERROR;
            }

            if (estado == Q_ERROR) {
                huboError = true;
                caracterError = c;
                posError = i;
                break;
            }
        }

        // Estados de aceptacion: uno por cada instruccion valida
        if (!huboError && estado == Q_MOV_NUM) {
            tokensOut.push_back({TipoToken::MOV, entrada.substr(mnemonico_inicio, mnemonico_final - mnemonico_inicio + 1)});
            tokensOut.push_back({TipoToken::REGISTRO, entrada.substr(registro_1_inicio, registro_1_final - registro_1_inicio + 1)});
            tokensOut.push_back({TipoToken::COMA, ","});
            tokensOut.push_back({TipoToken::NUMERO, entrada.substr(num_inicio, num_final - num_inicio + 1)});
            return true;
        }
        if (!huboError && estado == Q_ADD_BL || estado == Q_ADD_AL) {
            tokensOut.push_back({TipoToken::ADD, entrada.substr(mnemonico_inicio, mnemonico_final - mnemonico_inicio + 1)});
            tokensOut.push_back({TipoToken::REGISTRO, entrada.substr(registro_1_inicio, registro_1_final - registro_1_inicio + 1)});
            tokensOut.push_back({TipoToken::COMA, ","});
            tokensOut.push_back({TipoToken::REGISTRO, entrada.substr(registro_2_inicio, registro_2_final - registro_2_inicio + 1)});
            return true;
        }
        if (!huboError && estado == Q_STO_NUM) {
            tokensOut.push_back({TipoToken::STO, entrada.substr(mnemonico_inicio, mnemonico_final - mnemonico_inicio + 1)});
            tokensOut.push_back({TipoToken::NUMERO, entrada.substr(num_inicio, num_final - num_inicio + 1)});
            return true;
        }
        if (!huboError && estado == Q_END) {
            tokensOut.push_back({TipoToken::END, entrada.substr(mnemonico_inicio, mnemonico_final - mnemonico_inicio + 1)});
            return true;
        }

        // Estado no valido: armar el mensaje de error 
        if (huboError) {
            
            mensajeError = "Instruccion invalida: Se esperaba " + esperadoEn(estadoAnterior) + ".";
            /* mensajeError = "Instruccion invalida: caracter inesperado '" + string(1, caracterError) +
                            "' en la posicion " + to_string(posError) +
                            ". Se esperaba " + esperadoEn(estadoAnterior) + "."; */
        } else {
            mensajeError = "Instruccion invalida: Se esperaba " +
                            esperadoEn(estado) + ".";
        }
        return false;
    }
};

// SECCION 2: Objeto instruccion, se construye a partir de los tokens
struct ObjetoInstruccion {
    string operacion; 
    vector<string> registros; 
    bool tieneDireccion = false; // true si la instruccion tiene direccion de memoria, false si no
    int direccion = 0; // -1 significa "no tiene" (se imprime null)
};

static ObjetoInstruccion construirObjetoInstruccion(const vector<Token>& tokens) {
    ObjetoInstruccion obj;
    switch (tokens[0].tipo) {
        
        case TipoToken::MOV:
            obj.operacion = "MOV";
            obj.registros = { tokens[1].lexema }; 
            obj.tieneDireccion = true; 
            obj.direccion = stoi(tokens[3].lexema);
            break;
        case TipoToken::ADD:
            obj.operacion = "ADD";
            obj.registros = { tokens[1].lexema, tokens[3].lexema };
            break;
        case TipoToken::STO:
            obj.operacion = "STO";
            obj.tieneDireccion = true;
            obj.direccion = stoi(tokens[1].lexema);
            break;
        case TipoToken::END:
            obj.operacion = "END";
            break;
        default:
            break;
    }
    return obj;
}

// Imprime la lista de registros como un string en formato JSON
static string listaRegistrosStr(const vector<string>& regs) {
    string s = "[";
    for (size_t i = 0; i < regs.size(); i++) {
        s += "\"" + regs[i] + "\"";
        if (i + 1 < regs.size()) s += ", ";
    }
    s += "]";
    return s;
}

// SECCION 3: Maquina de Moore
enum class EstadoMoore { INICIO, PREPARAR_DIR, LEER_MEM, ESCRIBIR_MEM, FIN };

class MaquinaMoore {
public:
    // Constructor que inicializa la máquina con la instrucción a procesar
    explicit MaquinaMoore(const ObjetoInstruccion& instr)
        : instr_(instr), estado_(EstadoMoore::INICIO) {} 

    // Emite la salida asociada al estado actual y avanza al siguiente.
    // Regresa false cuando ya no hay mas microoperaciones (estado = Fin).
    bool siguientePaso(string& salida) {
        switch (estado_) {
            case EstadoMoore::INICIO:
                if (instr_.operacion == "MOV" || instr_.operacion == "STO") {
                    salida = "MAR <- " + to_string(instr_.direccion); // almacena la dirección en MAR (Memory Address Register)
                    estado_ = EstadoMoore::PREPARAR_DIR;
                    return true;
                }
                if (instr_.operacion == "ADD") {
                    salida = "ACC <- AL + BL"; // almacena la suma de AL y BL en ACC (Accumulator)
                    estado_ = EstadoMoore::FIN;
                    return true;
                }
                if (instr_.operacion == "END") {
                    salida = "HALT <- 1"; // indica que la ejecución debe detenerse
                    estado_ = EstadoMoore::FIN;
                    return true;
                }
                estado_ = EstadoMoore::FIN;
                return false;

            case EstadoMoore::PREPARAR_DIR:
                if (instr_.operacion == "MOV") {
                    salida = "MBR <- M[MAR]"; // "copia" el contenido de MAR en MBR (Memory Buffer Register)
                    estado_ = EstadoMoore::LEER_MEM;
                } else { // STO
                    salida = "MBR <- ACC"; // almacena el contenido del acumulador en MBR 
                    estado_ = EstadoMoore::ESCRIBIR_MEM;
                }
                return true;

            case EstadoMoore::LEER_MEM:
                salida = instr_.registros[0] + " <- MBR"; // almacena el contenido de MBR en el registro destino (AL o BL)
                estado_ = EstadoMoore::FIN;
                return true;

            case EstadoMoore::ESCRIBIR_MEM:
                salida = "M[MAR] <- MBR"; // almacena el contenido de MBR en la dirección de memoria apuntada por MAR
                estado_ = EstadoMoore::FIN;
                return true;

            case EstadoMoore::FIN:
            default:
                return false;
        }
    }

private:
    ObjetoInstruccion instr_;
    EstadoMoore estado_;
};

// SECCION 4: Procesamiento de una instruccion ingresada por el usuario
static void procesarInstruccion(const string& entradaOriginal) {
    string entrada = trim(entradaOriginal);

    cout << "\nENTRADA\n" << entrada << "\n\n";

    AFD afd; // instancia del AFD para validar la instrucción
    vector<Token> tokens; // vector para almacenar los tokens reconocidos
    string mensajeError; // mensaje de error si la instrucción es inválida

    cout << "VALIDACION MEDIANTE AFD\n";
    if (!afd.validar(entrada, tokens, mensajeError)) {
        cout << mensajeError << "\n";
        cout << "\nNo se construye el objeto instruccion.\n";
        cout << "No se generan microoperaciones.\n";
        cout << "\n--------------------------------------------------\n";
        cout << "Siguiente instruccion o presiona t para terminar.\n";
        return;
    }
    cout << "Instruccion valida.\n\n";

    cout << "TOKENS RECONOCIDOS\n";
    for (const auto& t : tokens) {
        cout << nombreToken(t.tipo) << "(\"" << t.lexema << "\")\n";
    }
    cout << "\n";

    ObjetoInstruccion obj = construirObjetoInstruccion(tokens);

    cout << "COMPONENTES IDENTIFICADOS\n";
    cout << "Mnemonico: " << obj.operacion << "\n";
    if (obj.operacion == "MOV") {
        cout << "Registro destino: " << obj.registros[0] << "\n";
        cout << "Direccion de memoria: " << obj.direccion << "\n";
        cout << "Direccionamiento: directo\n";
    } else if (obj.operacion == "ADD") {
        cout << "Registro 1: " << obj.registros[0] << "\n";
        cout << "Registro 2: " << obj.registros[1] << "\n";
    } else if (obj.operacion == "STO") {
        cout << "Direccion de memoria: " << obj.direccion << "\n";
        cout << "Direccionamiento: directo\n";
    } else {
        cout << "Sin operandos.\n";
    }
    cout << "\n";

    cout << "OBJETO INSTRUCCION\n";
    cout << "{\n";
    cout << "  operacion: \"" << obj.operacion << "\",\n";
    cout << "  registros: " << listaRegistrosStr(obj.registros) << ",\n";
    cout << "  direccion: " << (obj.tieneDireccion ? to_string(obj.direccion) : "null") << "\n";
    cout << "}\n\n";

    cout << "MICROOPERACIONES GENERADAS POR MOORE\n";
    MaquinaMoore moore(obj);
    string paso;
    int n = 1;
    while (moore.siguientePaso(paso)) {
        cout << n++ << ". " << paso << "\n";
    }
    cout << "\nGeneracion terminada.\n";
    cout << "\n--------------------------------------------------\n";
    cout << "Siguiente instruccion o presiona t para terminar.\n";
}

int main() {
    string linea;
    cout << "--------------------------------------------------\n";
    cout << "Ingrese la instruccion. Presiona t para terminar.\n";
    while (getline(cin, linea)) {
        string limpia = trim(linea);
        if (limpia.empty()) continue;

        if (limpia == "t" || limpia == "T") {
            cout << "--------------------------------------------------\n";
            cout << "Saliendo del programa...\n";
            break;
        }

        cout << "--------------------------------------------------\n";
        procesarInstruccion(linea);
    }
    return 0; 
}