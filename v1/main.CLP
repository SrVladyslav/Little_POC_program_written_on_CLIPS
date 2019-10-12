(deffacts datos
    ;VARIABLES ESTATICAS
    ;tipos de vagones tipo pesoMin pesoMax
    ;solucion sale a nivel 22

    (tipo T1 0 15);
    (tipo T2 16 23)


    ;(maleta Nombre peso origen destino)
    ;VARIABLES DINAMICAS
    (maleta M1 12 Fact P3)
    (maleta M2 18 Fact P5)
    (maleta M3 20 P1 Rec)
    (maleta M4 14 P6 Rec)



    ;informacion maletas
    ;para tener mas vagones, usar nmVag en tren
    ;tren posicion vagones tipo ubi enganchado maletas nombre cargada; 0 1

    ;(tren P6 vagones T1 P6 1 T2 P2 0 maletas M1 0 M2 0 M3 0 M4 0)
)

(defglobal ?*depth* = 0)
(defglobal ?*nodosGen* = 0)

(deffacts mapa
        (enlace P2 Fact)
        (enlace P2 P4)
        (enlace P4 P3)
        (enlace P4 P2)
        (enlace P3 P1)
        (enlace P3 P4)
    	(enlace P1 Fact)
   	(enlace P1 P5)
        (enlace P1 P3)
        (enlace Fact P2)
        (enlace Fact P1)
        (enlace P5 Rec)
        (enlace P5 P7)
        (enlace P5 P1)
        (enlace P7 P8)
        (enlace P7 P5)
        (enlace P8 P6)
        (enlace P8 P7)
        (enlace P6 Rec)
        (enlace P6 P8)
        (enlace Rec P5)
        (enlace Rec P6)
)

(defrule final
	(declare (salience 150))
  (max-depth ?userDepth)
	?f <- (tren ? vagones $?v maletas $?m)
	      (max-depth ?userDepth)
	(test (= (length $?m) 0))
	(test (>= ?userDepth ?*depth*))
    =>
	(printout t  "SOLUCION ENCONTRADA EN EL NIVEL " ?*depth* crlf)
	(printout t  "NUM DE NODOS EXPANDIDOS O REGLAS DISPARADAS " ?*nodosGen* crlf)
	(printout t  "HECHO OBJETIVO " ?f crlf)
	(halt)
)

(defrule noSolucion
	(declare (salience -50))
	?f <- (tren ? vagones $?v maletas $?m)
	      (max-depth ?userDepth)
	(test (<> (length $?m) 0))
	(test (< ?userDepth ?*depth*))
    =>
	(printout t  "SOLUCION NO ENCONTRADA EN EL NIVEL " ?*depth* crlf)
	(printout t  "NUM DE NODOS EXPANDIDOS O REGLAS DISPARADAS " ?*nodosGen* crlf)
	(halt)
)

;regla: $?a ?salida $?b ?destino $?c
;vagones tipo ubi maletas nombre peso origen destino

(defrule cargarMaleta
   	(declare (salience 25))
    (max-depth ?userDepth)
   	(tren ?pos vagones $?vt ?vagon ?posVagon 1 $?vt1 maletas $?c1 ?maleta 0 $?c3)
   	(maleta ?maleta ?peso ?origen ?)
   	(tipo ?tipo ?min ?max)
	  (test (eq ?pos ?origen )); maleta en donde vagon
	  (test (< ?peso ?max))
	  (test (> ?peso ?min))
	  (test (eq ?tipo ?vagon))
    (test (= ?pos ?posVagon))
    (test (>= ?userDepth ?*depth*))
	=>
	(assert (tren ?pos vagones $?vt ?vagon ?posVagon $?vt1 maletas $?c1 ?maleta 1 	$?c3))
	(bind ?*nodosGen* (+ ?*nodosGen* 1))
)

(defrule descargarMaleta
   (declare (salience 25))
   (max-depth ?userDepth)
   ?f0 <- (tren ?pos vagones $?vt ?vagon ?posVagon 1 $?vt1 maletas $?c1 ?maleta ?cargada $?c3)
   ?f1 <- (maleta ?maleta ?peso ? ?destino)
   ?f2 <- (tipo ?tipo ?min ?max)
    (test (eq ?pos ?destino)); maleta en donde vagon
    (test (= ?cargada 1));si esta cargada, es que esta en transito
    (test (< ?peso ?max))
    (test (> ?peso ?min))
    (test (eq ?tipo ?vagon))
    (test (= ?pos ?posVagon))
    (test (>= ?userDepth ?*depth*))
    ;Movidas con nombre y tipos de vagones
	  ;(test (=(mod (member$ ?vagon) 3) 0))
    ;(test (=(mod (member$ ?maleta) 2) 0))
	=>
	(retract ?f1)
	(assert (tren ?pos vagones $?vt ?vagon ?posVagon $?vt1 maletas $?c1 $?c3))
	(bind ?*nodosGen* (+ ?*nodosGen* 1))
)


;tren posicion vagones tipo ubi enganchado maletas nombre cargada;

(defrule engancharVagon
   (declare (salience 50))
   (max-depth ?userDepth)
    (tren ?pos vagones $?vt ?vagon ?posVagon ?enganchado $?vt1 maletas $?fin)
	  (test (eq ?pos ?posVagon))
    (test (>= ?userDepth ?*depth*))
	=>
	(assert (tren ?pos vagones $?vt ?vagon ?posVagon 1 $?vt1 maletas $?fin))
	(bind ?*nodosGen* (+ ?*nodosGen* 1))
)

(defrule desengancharVagon
   (declare (salience 100))
   (max-depth ?userDepth)
   ?f0 <- (tren ?pos vagones $?vt ?vagon ?posVagon ?enganchado $?vt1 maletas $?a ?cargada $?b)
   	(test (= ?enganchado 1))
	  (test (eq ?pos ?posVagon))
    (test (>= ?userDepth ?*depth*))
	=>
	(assert (tren ?pos vagones $?vt ?vagon ?posVagon 0 $?vt1 maletas $?a ?cargada $?b))
	(bind ?*nodosGen* (+ ?*nodosGen* 1))
)

;usar contadores para vagones �cuantas maletas lleva cada vag�n?


(defrule moverMaquina
    (max-depth ?userDepth)
    (tren ?origen vagones $?v maletas $?m)
    (enlace ?origen ?destino)
    (test (>= ?userDepth ?*depth*))
       =>
	  (assert (tren ?destino vagones $?v maletas $?m))
	  (bind ?*nodosGen* (+ ?*nodosGen* 1))
	  (bind ?*depth* (+ ?*depth* 1))
)

(deffunction inicio ()
	(reset)
	(printout t "Profundidad Maxima:= " )
	(bind ?userDepth (read))
	(printout t "Tipo de B�squeda " crlf "1.- Anchura" crlf
 					     "2.- Profundidad" crlf )
	(bind ?a (read))
	(if (= ?a 1)
 		then (set-strategy breadth)
 		else (set-strategy depth));)
	(assert (tren P6 vagones T1 P6 1 T2 P2 0 maletas M1 0 M2 0 M3 0 M4 0))
	(assert (max-depth ?userDepth))
)
